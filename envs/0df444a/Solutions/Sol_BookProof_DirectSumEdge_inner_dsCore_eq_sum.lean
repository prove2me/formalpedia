-- Prove2me | solution 1 for BookProof.DirectSumEdge.inner_dsCore_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:45:22.295359+00:00
-- url     : https://prove2.me/submissions/06a28fb7-bf59-471a-b8f8-3838188b4d14

-- Generated from ChapterDirectSumEdge.lean — solution of BookProof.DirectSumEdge.inner_dsCore_eq_sum
import Mathlib
import Definitions.Def_ChapterDirectSumEdge
import Theorems.Thm_BookProof_DirectSumEdge_coe_eq_zero_of_notMem_supportFinset
open BookProof.DirectSumEdge




open BookProof.FarisLavine BookProof.DirectSumEsa

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

set_option maxHeartbeats 1000000 in
theorem solution (x : dsCore D) (g : lp G 2) :
    (inner ℂ (x : lp G 2) g : ℂ)
      = ∑ i ∈ supportFinset x,
          (inner ℂ (((x : lp G 2) : ∀ i, G i) i) ((g : ∀ i, G i) i) : ℂ) := by

  rw [lp.inner_eq_tsum]
  refine tsum_eq_sum fun i hi => ?_
  rw [coe_eq_zero_of_notMem_supportFinset hi, inner_zero_left]
