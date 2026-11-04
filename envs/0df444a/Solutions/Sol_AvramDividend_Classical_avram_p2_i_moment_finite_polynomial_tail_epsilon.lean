-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_i_moment_finite_polynomial_tail_epsilon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:54:24.824949+00:00
-- url     : https://prove2.me/submissions/8da0aa9d-92cf-4d3a-adf4-972fb2abf73d

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_i_moment_finite_polynomial_high_power_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped BigOperators

theorem solution
    (s : Finset ℕ) (a : ℕ → ℝ) (n : ℕ)
    (hs : ∀ j ∈ s, j ≤ n) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, n ≤ K ∧ ∀ z : ℝ, 2 ≤ z →
      |∑ j ∈ s, a j * z ^ j| ≤ ε * z ^ K := by
  let C : ℝ := ∑ j ∈ s, |a j|
  have hp : Tendsto (fun r : ℕ => (2 : ℝ) ^ r) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  have he : ∀ᶠ r : ℕ in atTop, C / ε < (2 : ℝ) ^ r :=
    hp.eventually (eventually_gt_atTop _)
  obtain ⟨r, hr⟩ := he.exists
  have hC : C ≤ ε * (2 : ℝ) ^ r := by
    have ht := (div_lt_iff₀ hε).mp hr
    nlinarith
  refine ⟨n + r, Nat.le_add_right n r, ?_⟩
  intro z hz
  have hz0 : 0 ≤ z := by linarith
  have hzpow : 0 ≤ z ^ (n + r) := pow_nonneg hz0 _
  have ht := AvramDividend.Classical.avram_p2_i_moment_finite_polynomial_high_power_tail
    s a n r hs z hz
  have htwo : 0 < (2 : ℝ) ^ r := by positivity
  have hmul :
      (2 : ℝ) ^ r * |∑ j ∈ s, a j * z ^ j| ≤
        (2 : ℝ) ^ r * (ε * z ^ (n + r)) := by
    calc
      (2 : ℝ) ^ r * |∑ j ∈ s, a j * z ^ j| ≤
          C * z ^ (n + r) := ht
      _ ≤ (ε * (2 : ℝ) ^ r) * z ^ (n + r) :=
        mul_le_mul_of_nonneg_right hC hzpow
      _ = (2 : ℝ) ^ r * (ε * z ^ (n + r)) := by ring
  apply le_of_not_gt
  intro hgt
  have hstrict :
      0 < (2 : ℝ) ^ r *
        (|∑ j ∈ s, a j * z ^ j| - ε * z ^ (n + r)) :=
    mul_pos htwo (sub_pos.mpr hgt)
  nlinarith
