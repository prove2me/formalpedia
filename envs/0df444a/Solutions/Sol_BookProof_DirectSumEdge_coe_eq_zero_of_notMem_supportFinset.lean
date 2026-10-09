-- Prove2me | solution 1 for BookProof.DirectSumEdge.coe_eq_zero_of_notMem_supportFinset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T05:44:11.354737+00:00
-- url     : https://prove2.me/submissions/03c85c0f-955b-4f5d-87e2-d07f2f60fa50

-- Generated from ChapterDirectSumEdge.lean — solution of BookProof.DirectSumEdge.coe_eq_zero_of_notMem_supportFinset
import Mathlib
import Definitions.Def_ChapterDirectSumEdge
import Theorems.Thm_BookProof_DirectSumEdge_mem_supportFinset
open BookProof.DirectSumEdge




open BookProof.FarisLavine BookProof.DirectSumEsa

noncomputable section

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

variable {ι : Type*} {G : ι → Type*} [∀ i, NormedAddCommGroup (G i)]
  [∀ i, InnerProductSpace ℂ (G i)] {D : ∀ i, Submodule ℂ (G i)}

set_option maxHeartbeats 1000000 in
theorem solution {x : dsCore D} {i : ι}
    (hi : i ∉ supportFinset x) : ((x : lp G 2) : ∀ i, G i) i = 0 := by

  by_contra hne
  exact hi (mem_supportFinset.mpr hne)
