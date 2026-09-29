-- Prove2me | solution 1 for FamousTheorems.rees_depth_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:56:29.594655+00:00
-- url     : https://prove2.me/submissions/a22864f2-6e92-48a9-bcb4-7033d6f319e9

import Mathlib

universe v
open CategoryTheory

theorem solution {R : Type*} [CommRing R] [Small.{v} R] [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    (M : ModuleCat.{v} R) [Module.Finite R M] (hIM : I • (⊤ : Submodule R M) < ⊤) :
    List.TFAE [∀ N : ModuleCat.{v} R, Nontrivial N → Module.Finite R N →
        Module.support R N ⊆ PrimeSpectrum.zeroLocus (I : Set R) → ∀ i < n, Subsingleton (Abelian.Ext N M i),
      ∀ i < n, Subsingleton (Abelian.Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i),
      ∃ N : ModuleCat.{v} R, Nontrivial N ∧ Module.Finite R N ∧
        Module.support R N = PrimeSpectrum.zeroLocus (I : Set R) ∧ ∀ i < n, Subsingleton (Abelian.Ext N M i),
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs] :=
  ModuleCat.exists_isRegular_tfae I n M hIM
