-- Prove2me | solution 1 for FamousTheorems.structure_theorem_pid
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:10:25.343723+00:00
-- url     : https://prove2.me/submissions/ed07c0ec-1614-4df0-8872-71933d2a4b02

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution {R : Type u} [CommRing R] [IsPrincipalIdealRing R] [IsDomain R]
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (n : ℕ) (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i) (e : ι → ℕ),
      Nonempty <| M ≃ₗ[R] (Fin n →₀ R) × ⨁ i : ι, R ⧸ R ∙ p i ^ e i :=
  Module.equiv_free_prod_directSum R M
