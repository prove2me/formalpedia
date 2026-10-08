-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.creVec_eq_sum_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:18:02.27129+00:00
-- url     : https://prove2.me/submissions/d40ba1ef-ca8e-4703-973f-00d86ff7004b

-- Generated from ChapterFockNumberPreservingGap.lean — solution of BookProof.FockNumberPreservingGap.creVec_eq_sum_of_subset
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Theorems.Thm_BookProof_FockSecondQuantization_creVec_apply
open BookProof.FockNumberPreservingGap



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (v : ℕ →₀ ℂ) (x : FockAlg) {s : Finset ℕ}
    (h : v.support ⊆ s) : creVec v x = ∑ j ∈ s, v j • creA j x := by

  rw [creVec_apply]
  exact Finset.sum_subset h fun j _ hj => by
    rw [Finsupp.notMem_support_iff.mp hj, zero_smul]
