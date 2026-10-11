-- Prove2me | solution 1 for BookProof.TwoParticleSector.exists_ne_zero_bosonic
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:35:08.49912+00:00
-- url     : https://prove2.me/submissions/4794bce8-fc6e-49af-8eb5-3aa65b3d04d6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterTwoParticleSectorEsa.lean — solution of BookProof.TwoParticleSector.exists_ne_zero_bosonic
import Mathlib
import Definitions.Def_ChapterTwoParticleSectorEsa
import Theorems.Thm_BookProof_TwoParticleSector_mem_bosonic_iff
import Theorems.Thm_BookProof_TensorCore_tmul_mem_corePow
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterReducingSubspaceEsa
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.TwoParticleSector




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore

noncomputable section

variable (X : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X]
variable {X}
variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier)
variable (A : D₂ →ₗ[ℂ] Hs.carrier)
variable (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (hD : D ≤ D₂) {a : Hs.carrier} (haD : a ∈ D) (ha0 : a ≠ 0) :
    ∃ x : redDom (bosonicProj Hs) (sectorCore Hs D₂ D 2), x ≠ 0 := by

  set a' : D₂ := ⟨a, hD haD⟩ with ha'
  set v : (Hs.pow 2).carrier := a ⊗ₜ[ℂ] (a ⊗ₜ[ℂ] (1 : ℂ)) with hv
  have hcore : v ∈ sectorCore Hs D₂ D 2 :=
    ⟨a' ⊗ₜ[ℂ] (a' ⊗ₜ[ℂ] (1 : ℂ)),
      tmul_mem_corePow Hs D₂ D haD (tmul_mem_corePow Hs D₂ D haD (by trivial)), rfl⟩
  have hsec : v ∈ sector (bosonicProj Hs) := (mem_bosonic_iff Hs).mpr (by rw [hv, swapH_tmul])
  have hv0 : v ≠ 0 := by
    have hnorm : ‖v‖ = ‖a‖ * (‖a‖ * ‖(1 : ℂ)‖) := by
      rw [hv, TensorProduct.norm_tmul, TensorProduct.norm_tmul]
    intro h
    rw [h, norm_zero] at hnorm
    simp only [norm_one, mul_one] at hnorm
    exact ha0 (norm_eq_zero.mp (by nlinarith [norm_nonneg a]))
  refine ⟨⟨⟨v, hsec⟩, hcore⟩, ?_⟩
  intro h
  exact hv0 (by simpa using congrArg Subtype.val (congrArg Subtype.val h))
