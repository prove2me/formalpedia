-- Prove2me | solution 1 for AvramDividend.Classical.esscher_scale_deriv_lower_of_renewal_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:52:12.681554+00:00
-- url     : https://prove2.me/submissions/2b4d2d79-577c-4b7b-abc5-446b21041c69

import Theorems.Thm_AvramDividend_Classical_esscher_integrated_density_derivative_lower
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology Filter
open scoped Topology

/-- Differentiate the positive-axis renewal identity through an open-set equality. -/
theorem solution
    (W : ℝ → ℝ) (φ c : ℝ) (f k : ℝ → ℝ)
    (hφ : 0 ≤ φ)
    (hW : ∀ x : ℝ, 0 < x → W x =
      Real.exp (φ * x) * (c + ∫ t in (0 : ℝ)..x, f t))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (hmeas : ∀ x : ℝ, 0 < x → StronglyMeasurableAtFilter f (𝓝 x) volume)
    (hcont : ∀ x : ℝ, 0 < x → ContinuousAt f x)
    (hFnonneg : ∀ x : ℝ, 0 < x → 0 ≤ c + ∫ t in (0 : ℝ)..x, f t)
    (hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hk : ∀ x : ℝ, 0 < x → k x ≤ f x) :
    ∀ x : ℝ, 0 < x → k x ≤ deriv W x := by
  have heq : Set.EqOn W
      (fun y : ℝ => Real.exp (φ * y) *
        (c + ∫ t in (0 : ℝ)..y, f t)) (Ioi (0 : ℝ)) := by
    intro y hy
    exact hW y hy
  have hder := heq.deriv isOpen_Ioi
  intro x hx
  have hbound := esscher_integrated_density_derivative_lower φ c x f (k x)
    hφ hx.le (hint x hx) (hmeas x hx) (hcont x hx)
    (hFnonneg x hx) (hfnonneg x hx) (hk x hx)
  rw [hder hx]
  exact hbound
