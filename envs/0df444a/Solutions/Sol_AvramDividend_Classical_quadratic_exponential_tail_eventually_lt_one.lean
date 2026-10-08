-- Prove2me | solution 1 for AvramDividend.Classical.quadratic_exponential_tail_eventually_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T12:02:04.762848+00:00
-- url     : https://prove2.me/submissions/8595bd5f-748b-42aa-a840-1b05d77f85cd

import Mathlib

open Filter

theorem solution
    (a β0 C K : ℝ) (ha : 0 < a) :
    ∃ β : ℝ, β0 ≤ β ∧
      C * (1 + β ^ 2) *
        (Real.exp (-(β - β0) * a) * K) < 1 := by
  have h0 :
      Tendsto (fun x : ℝ => Real.exp (-a * x))
        atTop (nhds (0 : ℝ)) := by
    simpa only [Function.comp_def, id_eq, neg_mul] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.const_mul_atTop ha))
  have h2 :
      Tendsto (fun x : ℝ => x ^ (2 : ℕ) * Real.exp (-a * x))
        atTop (nhds (0 : ℝ)) := by
    have hp : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
      intro x
      simpa only [Nat.cast_ofNat] using
        (Real.rpow_natCast x (2 : ℕ))
    have hr :=
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (2 : ℝ) a ha
    apply hr.congr'
    filter_upwards with x
    rw [hp x]
  have hsum :
      Tendsto (fun x : ℝ => (1 + x ^ 2) * Real.exp (-a * x))
        atTop (nhds (0 : ℝ)) := by
    simpa only [add_mul, one_mul, zero_add] using h0.add h2
  have htarget :
      Tendsto
        (fun x : ℝ =>
          C * (1 + x ^ 2) *
            (Real.exp (-(x - β0) * a) * K))
        atTop (nhds (0 : ℝ)) := by
    have h := hsum.const_mul (C * Real.exp (β0 * a) * K)
    have h' :
        Tendsto
          (fun x : ℝ =>
            (C * Real.exp (β0 * a) * K) *
              ((1 + x ^ 2) * Real.exp (-a * x)))
          atTop (nhds (0 : ℝ)) := by
      simpa only [mul_zero] using h
    apply h'.congr'
    filter_upwards with x
    have he :
        Real.exp (-(x - β0) * a) =
          Real.exp (-a * x) * Real.exp (β0 * a) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  have hsmall :
      ∀ᶠ x : ℝ in atTop,
        C * (1 + x ^ 2) *
          (Real.exp (-(x - β0) * a) * K) < 1 :=
    htarget.eventually_lt_const (by norm_num : (0 : ℝ) < 1)
  have hlarge : ∀ᶠ x : ℝ in atTop, β0 ≤ x :=
    eventually_ge_atTop β0
  obtain ⟨β, hβ⟩ := (hlarge.and hsmall).exists
  exact ⟨β, hβ.1, hβ.2⟩
