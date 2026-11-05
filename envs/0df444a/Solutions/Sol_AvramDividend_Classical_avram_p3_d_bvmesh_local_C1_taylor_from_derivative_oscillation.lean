-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_d_bvmesh_local_C1_taylor_from_derivative_oscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:10:08.761221+00:00
-- url     : https://prove2.me/submissions/4dfd2087-0e0e-4dd0-9327-0f0d4bedc140

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- The Taylor remainder is controlled by derivative oscillation on the actual
closed source segment. No derivative outside that segment is assumed. -/
theorem solution
    (f : ℝ → ℝ) (a b ε : ℝ)
    (hdiff : ∀ x ∈ Set.uIcc a b, DifferentiableAt ℝ f x)
    (hInt : IntervalIntegrable (deriv f) volume a b)
    (hosc : ∀ x ∈ Set.uIoc a b, |deriv f x - deriv f a| ≤ ε) :
    |f b - f a - deriv f a * (b - a)| ≤ ε * |b - a| := by
  have hFTC : (∫ x in a..b, deriv f x) = f b - f a :=
    intervalIntegral.integral_deriv_eq_sub hdiff hInt
  have hconstInt :
      IntervalIntegrable (fun _ : ℝ => deriv f a) volume a b :=
    intervalIntegrable_const
  have hconst : (∫ x in a..b, deriv f a) =
      (b - a) * deriv f a := by
    exact intervalIntegral.integral_const (deriv f a)
  have hsub :
      (∫ x in a..b, deriv f x - deriv f a) =
        (∫ x in a..b, deriv f x) -
        (∫ x in a..b, deriv f a) :=
    intervalIntegral.integral_sub hInt hconstInt
  have hrepr :
      f b - f a - deriv f a * (b - a) =
        (∫ x in a..b, deriv f x - deriv f a) := by
    rw [hsub, hFTC, hconst]
    ring
  have hbound (x : ℝ) (hx : x ∈ Set.uIoc a b) :
      ‖deriv f x - deriv f a‖ ≤ ε := by
    simpa only [Real.norm_eq_abs] using hosc x hx
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (C := ε) hbound
  rw [hrepr]
  simpa only [Real.norm_eq_abs] using hnorm
