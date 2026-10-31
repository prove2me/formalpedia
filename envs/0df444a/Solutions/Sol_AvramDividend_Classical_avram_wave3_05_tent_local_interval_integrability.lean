-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_tent_local_interval_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T09:47:36.874549+00:00
-- url     : https://prove2.me/submissions/7b460470-f601-47bf-baa6-531c186f47e2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral

/-- Gaussian C² regularity makes the two interior triangular Taylor
    kernels interval-integrable on every positive reserve segment. -/
theorem solution
    (F : ℝ → ℝ) (hF : ContinuousOn F (Ioi (0 : ℝ)))
    (r x θ : ℝ) (hr : 0 ≤ r) (hx : r < x) :
    IntervalIntegrable (fun s : ℝ => (r - s) * F (x - s)) volume 0 r ∧
      IntervalIntegrable (fun s : ℝ =>
        (r - s) * Real.exp (-θ * (x - s)) * |F (x - s)|)
        volume 0 r := by
  have hsub : Continuous (fun s : ℝ => x - s) :=
    continuous_const.sub continuous_id
  have hmaps : MapsTo (fun s : ℝ => x - s) (Icc (0 : ℝ) r) (Ioi 0) := by
    intro s hs
    exact sub_pos.mpr (lt_of_le_of_lt hs.2 hx)
  have hFc : ContinuousOn (fun s : ℝ => F (x - s)) (Icc 0 r) :=
    hF.comp hsub.continuousOn hmaps
  have hlinear : Continuous (fun s : ℝ => r - s) :=
    continuous_const.sub continuous_id
  have hweight : Continuous (fun s : ℝ => Real.exp (-θ * (x - s))) := by
    fun_prop
  have hfirst : ContinuousOn
      (fun s : ℝ => (r - s) * F (x - s)) (Icc 0 r) :=
    hlinear.continuousOn.mul hFc
  have hsecond : ContinuousOn
      (fun s : ℝ => (r - s) * Real.exp (-θ * (x - s)) * |F (x - s)|)
      (Icc 0 r) :=
    (hlinear.continuousOn.mul hweight.continuousOn).mul hFc.abs
  exact ⟨hfirst.intervalIntegrable_of_Icc hr,
    hsecond.intervalIntegrable_of_Icc hr⟩
