-- Prove2me | solution 1 for BookProof.ChapterCoherentOccupation.hasSum_expSeries
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:10:59.596261+00:00
-- url     : https://prove2.me/submissions/b8ca1ff6-99a0-4204-875a-839a455847a5

-- Generated from ChapterCoherentOccupation.lean — solution of BookProof.ChapterCoherentOccupation.hasSum_expSeries
import Mathlib
import Definitions.Def_ChapterCoherentOccupation
open BookProof.ChapterCoherentOccupation



noncomputable section


open Real Nat ProbabilityTheory

set_option maxHeartbeats 1000000 in
theorem solution (lam : ℝ) :
    HasSum (fun n : ℕ => lam ^ n / (n ! : ℝ)) (Real.exp lam) := by

  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  exact (Real.summable_pow_div_factorial lam).hasSum
