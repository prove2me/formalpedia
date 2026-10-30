-- Prove2me | solution 1 for AvramDividend.Classical.tilted_scale_integrated_rep_of_C1_esscher_49ac_gap
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:44:23.518232+00:00
-- url     : https://prove2.me/submissions/003d32f9-dda9-4c37-8839-4e2b6e441c90

import Mathlib
open MeasureTheory Set Topology
open scoped NNReal ENNReal

lemma tilt_aux
    (V tail : ℝ → ℝ)
    (hVpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hVdiff : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)))
    (hder : ∀ x : ℝ, 0 < x → deriv V x = V x * tail x)
    (hcont : ContinuousOn tail (Ioi (0 : ℝ))) :
    ∀ a b : ℝ, 0 < a → a ≤ b →
      V b = V a * Real.exp (∫ t in a..b, tail t) := by
  intro a b ha hab
  have hVd : ∀ x : ℝ, 0 < x → HasDerivAt V (V x * tail x) x := by
    intro x hx
    have h1 : ContDiffAt ℝ 1 V x := hVdiff.contDiffAt (Ioi_mem_nhds hx)
    have h2 : DifferentiableAt ℝ V x := h1.differentiableAt one_ne_zero
    have := h2.hasDerivAt
    rwa [hder x hx] at this
  have hlog : ∀ x ∈ uIcc a b, HasDerivAt (fun y => Real.log (V y)) (tail x) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
    have := (hVd x hx0).log (hVpos x hx0).ne'
    have e : V x * tail x / V x = tail x := by
      field_simp [(hVpos x hx0).ne']
    rwa [e] at this
  have hint : IntervalIntegrable tail volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hcont.mono (fun x hx => lt_of_lt_of_le ha hx.1)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hlog hint
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  rw [hftc, Real.exp_sub, Real.exp_log (hVpos b hb0), Real.exp_log (hVpos a ha)]
  field_simp [(hVpos a ha).ne']

theorem solution
    (W V tail : ℝ → ℝ) (φ : ℝ)
    (hEsscher : ∀ x : ℝ, 0 < x → W x = Real.exp (φ * x) * V x)
    (hVpos : ∀ x : ℝ, 0 < x → 0 < V x)
    (hVdiff : ContDiffOn ℝ 1 V (Ioi (0 : ℝ)))
    (hder : ∀ x : ℝ, 0 < x → deriv V x = V x * tail x)
    (hcont : ContinuousOn tail (Ioi (0 : ℝ))) :
    ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + tail t) := by
  intro a b ha hab
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hV := tilt_aux V tail hVpos hVdiff hder hcont a b ha hab
  have hint : IntervalIntegrable tail volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hcont.mono (fun x hx => lt_of_lt_of_le ha hx.1)
  rw [intervalIntegral.integral_add intervalIntegrable_const hint]
  rw [hEsscher a ha, hEsscher b hb0, hV]
  simp only [intervalIntegral.integral_const, smul_eq_mul]
  rw [Real.exp_add, ← mul_assoc, ← mul_assoc]
  have : Real.exp (φ * b) = Real.exp (φ * a) * Real.exp ((b - a) * φ) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring
