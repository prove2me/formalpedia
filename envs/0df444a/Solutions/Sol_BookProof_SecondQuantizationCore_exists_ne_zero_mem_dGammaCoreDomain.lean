-- Prove2me | solution 1 for BookProof.SecondQuantizationCore.exists_ne_zero_mem_dGammaCoreDomain
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T20:19:19.004881+00:00
-- url     : https://prove2.me/submissions/4776b71f-f5b4-4a5c-a2df-354ccb62c7d8

-- Generated from ChapterSecondQuantizationCoreEsa.lean — solution of BookProof.SecondQuantizationCore.exists_ne_zero_mem_dGammaCoreDomain
import Mathlib
import Definitions.Def_ChapterSecondQuantizationCoreEsa
import Theorems.Thm_BookProof_GraphCore_mem_pushDom
import Theorems.Thm_BookProof_TensorCore_exists_ne_zero_mem_sectorCore_one
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterGraphCoreTransfer
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterTensorGraphCore
open BookProof.SecondQuantizationCore




open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.DirectSumEsa
open BookProof.DirectSumEsa
open BookProof.TensorCore

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

set_option maxHeartbeats 1000000 in
theorem solution (hD : D ≤ D₂) {a : Hs.carrier} (haD : a ∈ D)
    (ha0 : a ≠ 0) :
    ∃ f ∈ dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n), f ≠ 0 := by

  classical
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_mem_sectorCore_one Hs D₂ D hD haD ha0
  refine ⟨lp.single 2 1 (sectorEmb Hs 1 x), ⟨?_, ?_⟩, ?_⟩
  · refine Set.Finite.subset (Set.finite_singleton 1) (fun i hi => ?_)
    simp only [Set.mem_setOf_eq, lp.single_apply] at hi
    by_contra hne
    exact hi (Pi.single_eq_of_ne (by simpa using hne) _)
  · intro i
    rw [lp.single_apply]
    by_cases hi : i = 1
    · subst hi
      rw [Pi.single_eq_same]
      exact mem_pushDom (sectorEmb Hs 1) (⟨x, hx⟩ : sectorCore Hs D₂ D 1)
    · rw [Pi.single_eq_of_ne hi]
      exact Submodule.zero_mem _
  · intro hzero
    have hnorm : ‖lp.single 2 1 (sectorEmb Hs 1 x)‖ = ‖x‖ := by
      rw [lp.norm_single (by norm_num) 1 (sectorEmb Hs 1 x), (sectorEmb Hs 1).norm_map]
    rw [hzero, norm_zero] at hnorm
    exact hx0 (norm_eq_zero.mp hnorm.symm)
