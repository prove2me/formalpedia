-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.creVec_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:19:17.424037+00:00
-- url     : https://prove2.me/submissions/b985c712-e61a-43b3-9142-681c84e473e6

-- Generated from ChapterFockNumberPreservingGap.lean — solution of BookProof.FockNumberPreservingGap.creVec_smul
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Theorems.Thm_BookProof_FockNumberPreservingGap_creVec_eq_sum_of_subset
import Theorems.Thm_BookProof_FockSecondQuantization_creVec_apply
open BookProof.FockNumberPreservingGap



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution (c : ℂ) (v : ℕ →₀ ℂ) (x : FockAlg) :
    creVec (c • v) x = c • creVec v x := by

  classical
  have h1 : (c • v).support ⊆ v.support := Finsupp.support_smul
  rw [creVec_eq_sum_of_subset _ _ h1, creVec_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, mul_smul]
