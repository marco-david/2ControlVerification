{
  description = "Local development environment for 2ControlVerification";
  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixos-23.11";
    nixpkgs-unstable.url = "github:nixos/nixpkgs/nixos-unstable";
  };

  outputs =
    {
      self,
      nixpkgs,
      nixpkgs-unstable,
    }:
    let
      system = "x86_64-linux";
      pkgs = nixpkgs.legacyPackages.${system};
      pkgs-unstable = nixpkgs-unstable.legacyPackages.${system};
      coq-quantumlib-version = "v1.5.0";
    in
    let
      coq-quantumlib = pkgs.coqPackages.mkCoqDerivation {
        pname = "quantumlib";
        owner = "inQWIRE";
        repo = "QuantumLib";

        defaultVersion = coq-quantumlib-version;
        release.${coq-quantumlib-version} = {
          rev = "ee147b9c18265cb22b780b9dce8d5a386a78b807";
          sha256 = "sha256-3zGrJPQZzxtRpEQa1J4vrI6hnxoq4hhXvyL7pWipxwU=";
        };
        useDune = true;
      };
    in
    {
      devShell.${system} = pkgs.mkShell {
        packages =
          [
            pkgs.coq
            pkgs.coq.ocamlPackages.ocaml
            pkgs.coq.ocamlPackages.dune_3
            coq-quantumlib
          ]
          ++ pkgs.lib.optional (builtins.getEnv "CI" != "true") (
            pkgs.coqPackages.coq-lsp.override { coq = pkgs.coq_8_18; }
          ); # Don't build the LSP in GitHub Action
      };
    };
}
