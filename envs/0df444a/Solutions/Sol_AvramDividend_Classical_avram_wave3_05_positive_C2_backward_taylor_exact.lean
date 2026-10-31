-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_positive_C2_backward_taylor_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T08:25:52.26727+00:00
-- url     : https://prove2.me/submissions/be714ccb-5ed4-408c-9f11-543f5a4c2f13

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory

/-- Positive-axis second-order Taylor remainder for the original scale-function generator interior. -/
theorem solution
    (f : ℝ → ℝ) (hf : ContDiffOn ℝ 2 f (Ioi 0))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    f a - f b + (b - a) * deriv f b =
      ∫ t in a..b, (t - a) * iteratedDeriv 2 f t := by
  have hsub : Icc a b ⊆ Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_lt_of_le ha ht.1
  have hcd : ContDiffOn ℝ 2 f (Icc a b) := hf.mono hsub
  have hT := taylor_integral_remainder (f := f) (x := a)
      (x₀ := b) (n := 1) (by simpa [uIcc_of_ge hab.le] using hcd)
  have huniq : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hbd : ContDiffAt ℝ 2 f b :=
    hf.contDiffAt (isOpen_Ioi.mem_nhds (lt_trans ha hab))
  have hD : iteratedDerivWithin 1 f (Icc a b) b = deriv f b := by
    simpa only [iteratedDeriv_one] using
      (iteratedDerivWithin_eq_iteratedDeriv (n := 1) huniq
        (hbd.of_le (by norm_num)) ⟨hab.le, le_refl b⟩)
  have hD2 : ∀ t ∈ Icc a b,
      iteratedDerivWithin 2 f (Icc a b) t = iteratedDeriv 2 f t := by
    intro t ht
    exact iteratedDerivWithin_eq_iteratedDeriv huniq
      (hf.contDiffAt (isOpen_Ioi.mem_nhds (lt_of_lt_of_le ha ht.1))) ht
  simp only [uIcc_of_ge hab.le] at hT
  simp only [taylorWithinEval_succ, taylor_within_zero_eval,
    iteratedDerivWithin_zero, Nat.factorial_zero, Nat.cast_one,
    one_mul, one_pow, inv_one, smul_eq_mul] at hT
  rw [hD] at hT
  norm_num at hT
  have hI : (∫ t in b..a, (a - t) * iteratedDerivWithin 2 f (Icc a b) t) =
      ∫ t in b..a, (a - t) * iteratedDeriv 2 f t := by
    apply intervalIntegral.integral_congr
    intro t ht
    change (a - t) * iteratedDerivWithin 2 f (Icc a b) t =
      (a - t) * iteratedDeriv 2 f t
    rw [hD2 t (by simpa [uIcc_of_ge hab.le] using ht)]
  rw [hI] at hT
  rw [intervalIntegral.integral_symm] at hT
  calc
    f a - f b + (b - a) * deriv f b =
        f a - (f b + (a - b) * deriv f b) := by ring
    _ = -(∫ t in a..b, (a - t) * iteratedDeriv 2 f t) := hT
    _ = ∫ t in a..b, (t - a) * iteratedDeriv 2 f t := by
      rw [← intervalIntegral.integral_neg]
      congr 1
      funext t
      ring
