-- Prove2me | solution 1 for AvramDividend.Classical.avram_a19_singular_profile_unbounded_below
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T08:59:55.499688+00:00
-- url     : https://prove2.me/submissions/9134e4b9-0bcc-4815-8d2b-3c37e23acb3e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- The explicit singular HJB profile has no finite lower bound near zero. -/
theorem solution (B : Real) :
    Exists (fun t : Real => And (0 < t)
      (And (t < 1) (3 + t ^ 2 - 4 * t - 2 / t < B))) := by
  let s : Real := abs B + 10
  have hs : 1 < s := by
    dsimp [s]
    have h := abs_nonneg B
    linarith
  have hpos : 0 < s := by linarith
  let t : Real := 1 / s
  have htpos : 0 < t := by
    dsimp [t]
    exact div_pos (by norm_num) hpos
  have hprod : s * t = 1 := by
    dsimp [t]
    field_simp [ne_of_gt hpos]
  have htlt : t < 1 := by
    have hp : 0 < (s - 1) * t := mul_pos (by linarith) htpos
    nlinarith
  have hsq : t ^ 2 <= 1 := by nlinarith
  have hdiv : 2 / t = 2 * s := by
    dsimp [t]
    field_simp [ne_of_gt hpos]
  refine Exists.intro t (And.intro htpos (And.intro htlt ?_))
  rw [hdiv]
  have hB : -(abs B) <= B := neg_abs_le B
  dsimp [s] at *
  nlinarith [htpos]
