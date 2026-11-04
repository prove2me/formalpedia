-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_b_rate_separated_test_function_weight_domination
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:38:20.178968+00:00
-- url     : https://prove2.me/submissions/54a30b8b-9f58-4030-a663-f7c8f9fd3150

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (f : ℝ → ℝ) (M θ ε : ℝ)
    (hM : 0 ≤ M) (hfbound : ∀ y, |f y| ≤ M)
    (hfsupp : ∀ y, -ε < y → f y = 0)
    (hθ : 0 < θ) (hε : 0 < ε) :
    ∀ y : ℝ, |f y| ≤
      (M / (1 - Real.exp (-θ * ε)) ^ 4) *
        (Real.exp (θ * y) - 1) ^ 4 := by
  let k : ℝ := (1 - Real.exp (-θ * ε)) ^ 4
  have hneg : -θ * ε < 0 := by
    nlinarith [mul_pos hθ hε]
  have he : Real.exp (-θ * ε) < 1 := by
    have h := Real.exp_lt_exp.mpr hneg
    simpa using h
  have hk : 0 < k := by
    dsimp [k]
    have hh : 0 < 1 - Real.exp (-θ * ε) := by linarith
    positivity
  have hq : 0 ≤ M / k := div_nonneg hM hk.le
  have hcancel : (M / k) * k = M := by
    field_simp [ne_of_gt hk]
  change ∀ y : ℝ, |f y| ≤ (M / k) *
    (Real.exp (θ * y) - 1) ^ 4
  intro y
  by_cases hy : y ≤ -ε
  · have hm : θ * y ≤ -θ * ε := by
      have hz := mul_le_mul_of_nonneg_left hy hθ.le
      nlinarith
    have hx : Real.exp (θ * y) ≤ Real.exp (-θ * ε) :=
      Real.exp_le_exp.mpr hm
    have hw : k ≤ (Real.exp (θ * y) - 1) ^ 4 := by
      dsimp [k]
      calc
        (1 - Real.exp (-θ * ε)) ^ 4 ≤
            (1 - Real.exp (θ * y)) ^ 4 := by
              gcongr
        _ = (Real.exp (θ * y) - 1) ^ 4 := by ring
    have hmul := mul_le_mul_of_nonneg_left hw hq
    linarith [hfbound y]
  · have hf : f y = 0 := hfsupp y (lt_of_not_ge hy)
    rw [hf, abs_zero]
    exact mul_nonneg hq (by positivity)
