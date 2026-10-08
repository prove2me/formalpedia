-- Prove2me | solution 1 for AvramDividend.Classical.excursion_integral_scale_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:41:51.227988+00:00
-- url     : https://prove2.me/submissions/335e9bf2-62f6-4047-9db5-7a408d3bb35c

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem solution
    (W : ℝ → ℝ) (φ : ℝ) (μ : Measure ℝ)
    (hcont : ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi 0))
    (hexp : ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t))) :
    ∀ x : ℝ, 0 < x →
      HasDerivAt W (W x * (φ + μ.real (Ici x))) x := by
  intro x hx
  let g : ℝ → ℝ := fun t => φ + μ.real (Ici t)
  have hgcont : ContinuousOn g (Ioi (0 : ℝ)) := by
    change ContinuousOn
      ((fun _ : ℝ => φ) + (fun t : ℝ => μ.real (Ici t))) (Ioi (0 : ℝ))
    exact continuousOn_const.add hcont
  have hcx : ContinuousAt g x :=
    hgcont.continuousAt (isOpen_Ioi.mem_nhds hx)
  let a : ℝ := x / 2
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hax : a < x := by
    dsimp [a]
    linarith
  have hsub : Icc a x ⊆ Ioi (0 : ℝ) := by
    intro y hy
    exact lt_of_lt_of_le ha hy.1
  have hint : IntervalIntegrable g volume a x :=
    ContinuousOn.intervalIntegrable_of_Icc (le_of_lt hax) (hgcont.mono hsub)
  have hmeas : StronglyMeasurableAtFilter g (𝓝 x) volume :=
    hgcont.stronglyMeasurableAtFilter isOpen_Ioi x hx
  have hfund :
      HasDerivAt (fun y : ℝ => ∫ t in a..y, g t) (g x) x :=
    intervalIntegral.integral_hasDerivAt_right hint hmeas hcx
  have hmodel :
      HasDerivAt
        (fun y : ℝ => W a * Real.exp (∫ t in a..y, g t))
        (W a * (Real.exp (∫ t in a..x, g t) * g x)) x := by
    simpa only using (hfund.exp.const_mul (W a))
  have hlocal :
      W =ᶠ[𝓝 x] (fun y : ℝ =>
        W a * Real.exp (∫ t in a..y, g t)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hax] with y hy
    simpa only [g] using hexp a y ha (le_of_lt hy)
  have hWmodel : W x = W a * Real.exp (∫ t in a..x, g t) := by
    simpa only [g] using hexp a x ha (le_of_lt hax)
  have hderiv :
      HasDerivAt W
        (W a * (Real.exp (∫ t in a..x, g t) * g x)) x :=
    hmodel.congr_of_eventuallyEq hlocal
  have hresult : HasDerivAt W (W x * g x) x := by
    convert hderiv using 1
    rw [hWmodel]
    ring
  simpa only [g] using hresult
