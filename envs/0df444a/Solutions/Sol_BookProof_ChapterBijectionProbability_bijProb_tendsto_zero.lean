-- Prove2me | solution 1 for BookProof.ChapterBijectionProbability.bijProb_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T19:28:35.513033+00:00
-- url     : https://prove2.me/submissions/264e3083-1e5f-4172-a674-5d0331f91107

-- Generated from ChapterBijectionProbability.lean — solution of BookProof.ChapterBijectionProbability.bijProb_tendsto_zero
import Mathlib
import Definitions.Def_ChapterBijectionProbability
import Theorems.Thm_BookProof_ChapterBijectionProbability_bijProb_nonneg
import Theorems.Thm_BookProof_ChapterBijectionProbability_bijProb_le_one_div
open BookProof.ChapterBijectionProbability



open scoped Nat
open Filter Asymptotics

set_option maxHeartbeats 1000000 in
theorem solution : Tendsto bijProb atTop (nhds 0) := by

  apply squeeze_zero' (f := bijProb) (g := fun n : ℕ => 1 / (n : ℝ))
  · exact Eventually.of_forall bijProb_nonneg
  · filter_upwards [eventually_ge_atTop 1] with n hn using bijProb_le_one_div n hn
  · exact tendsto_one_div_atTop_nhds_zero_nat
