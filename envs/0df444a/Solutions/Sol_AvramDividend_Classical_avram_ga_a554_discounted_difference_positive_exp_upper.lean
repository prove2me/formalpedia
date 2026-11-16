-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a554_discounted_difference_positive_exp_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T08:05:05.836973+00:00
-- url     : https://prove2.me/submissions/1a492686-c930-49a5-b608-3a7357f8853f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
noncomputable section

theorem solution
    (a b e θ K M z : ℝ)
    (hK : 0 ≤ K) (hM : 0 ≤ M)
    (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (ha : a ≤ K * Real.exp (θ * z))
    (hb : |b| ≤ M) :
    max (e * (a - b)) (0 : ℝ) ≤
      K * Real.exp (θ * z) + M := by
  have hright : 0 ≤ K * Real.exp (θ * z) + M :=
    add_nonneg (mul_nonneg hK (Real.exp_pos _).le) hM
  have hdiff : a - b ≤ K * Real.exp (θ * z) + M := by
    have hb' := (abs_le.mp hb).1
    linarith
  apply max_le
  · by_cases hp : 0 ≤ a - b
    · have he := mul_le_mul_of_nonneg_right he1 hp
      nlinarith
    · have he := mul_nonpos_of_nonneg_of_nonpos he0 (le_of_not_ge hp)
      exact he.trans hright
  · exact hright
