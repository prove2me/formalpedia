-- Prove2me | solution 1 for BookProof.ChapterEntropy.invertibleProb_isEquivalent_stirling
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:40:06.87912+00:00
-- url     : https://prove2.me/submissions/dc487165-dbf1-4028-a6e7-fc688e65a480

-- Generated from ChapterEntropy.lean — solution of BookProof.ChapterEntropy.invertibleProb_isEquivalent_stirling
import Mathlib
import Definitions.Def_ChapterEntropy
import Theorems.Thm_BookProof_ChapterEntropy_card_bijections
open BookProof.ChapterEntropy




open Filter Asymptotics
open scoped Topology

set_option maxHeartbeats 1000000 in
theorem solution :
    invertibleProb ~[atTop]
      (fun n : ℕ => Real.sqrt (2 * Real.pi * n) * Real.exp (-(n : ℝ))) := by

  -- Stirling's approximation to the factorial function, with `2πn` reordered.
  have h_stirling :
      (fun n : ℕ => (Nat.factorial n : ℝ)) ~[atTop]
        (fun n : ℕ => Real.sqrt (2 * Real.pi * n) * (n / Real.exp 1) ^ n) := by
    convert Stirling.factorial_isEquivalent_stirling using 1
    ac_rfl
  -- Divide both sides by `nⁿ`.
  convert h_stirling.div
      (show (fun n : ℕ => (n ^ n : ℝ)) ~[atTop] (fun n : ℕ => (n ^ n : ℝ)) from ?_) using 1
  · ext n; simp [invertibleProb, card_bijections]
  · ext n
    norm_num [Real.exp_neg, div_pow]
    ring_nf
    by_cases h : (n : ℝ) = 0 <;> simp [h]
  · rfl
