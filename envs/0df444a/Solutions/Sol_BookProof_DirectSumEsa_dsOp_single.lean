-- Prove2me | solution 1 for BookProof.DirectSumEsa.dsOp_single
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T14:15:42.007177+00:00
-- url     : https://prove2.me/submissions/3d57671f-98ca-4a13-a149-2d05521d9c9c

-- Generated from ChapterDirectSumEsa.lean — solution of BookProof.DirectSumEsa.dsOp_single
import Mathlib
import Definitions.Def_ChapterDirectSumEsa
import Theorems.Thm_BookProof_DirectSumEsa_single_mem_dsCore
import Definitions.Def_ChapterFarisLavine
open BookProof.DirectSumEsa



open scoped ENNReal


open BookProof.FarisLavine

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)]
variable {D : ∀ i, Submodule ℂ (G i)}

set_option maxHeartbeats 1000000 in
theorem solution [DecidableEq ι] (H : ∀ i, D i →ₗ[ℂ] G i) (i : ι) (u : D i) :
    (dsOp H ⟨lp.single 2 i ((u : G i)), single_mem_dsCore i u⟩ : lp G 2)
      = lp.single 2 i (H i u) := by

  classical
  refine lp.ext (funext fun j => ?_)
  rw [lp.single_apply]
  have hcoe : ((dsOp H ⟨lp.single 2 i ((u : G i)), single_mem_dsCore i u⟩ : lp G 2)
      : ∀ i, G i) j
      = H j ⟨(lp.single 2 i ((u : G i)) : lp G 2) j, (single_mem_dsCore i u).2 j⟩ := rfl
  rw [hcoe]
  by_cases hj : j = i
  · subst hj
    have hu : (⟨(lp.single 2 j ((u : G j)) : lp G 2) j, (single_mem_dsCore j u).2 j⟩ : D j)
        = u := Subtype.ext (by
          change (lp.single 2 j ((u : G j)) : lp G 2) j = (u : G j)
          rw [lp.single_apply, Pi.single_eq_same])
    rw [Pi.single_eq_same]
    exact congrArg (H j) hu
  · have hzero : (⟨(lp.single 2 i ((u : G i)) : lp G 2) j, (single_mem_dsCore i u).2 j⟩ : D j)
        = 0 := Subtype.ext (by
          change (lp.single 2 i ((u : G i)) : lp G 2) j = (0 : G j)
          rw [lp.single_apply, Pi.single_eq_of_ne hj])
    rw [Pi.single_eq_of_ne hj]
    exact (congrArg (H j) hzero).trans (map_zero (H j))
