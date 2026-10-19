-- Prove2me | solution 1 for CompactnessConjecture.symplectic_isotropic_finrank_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:35:57.541617+00:00
-- url     : https://prove2.me/submissions/e4eec07b-3306-41ad-aca4-71c4ba2ceb00

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open CompactnessConjecture
noncomputable section
open SimpleGraph
variable (K : Type*) [Field K]
namespace CompactnessConjecture
theorem _root_.solution
    (S : Submodule K (SymplecticVector K))
    (hS : ∀ u ∈ S, ∀ v ∈ S,
      standardSymplecticForm K u v = 0) :
    Module.finrank K S ≤ 2 := by
  have hle : S ≤ (standardSymplecticBilin K).orthogonal S := by
    intro x hx
    change ∀ y ∈ S, standardSymplecticForm K y x = 0
    intro y hy
    exact hS y hy x hx
  have hrank := Submodule.finrank_mono hle
  rw [LinearMap.BilinForm.finrank_orthogonal
    (standardSymplecticBilin_nondegenerate K)] at hrank
  have hambient : Module.finrank K (SymplecticVector K) = 4 := by
    simp [SymplecticVector]
  rw [hambient] at hrank
  omega
end CompactnessConjecture
