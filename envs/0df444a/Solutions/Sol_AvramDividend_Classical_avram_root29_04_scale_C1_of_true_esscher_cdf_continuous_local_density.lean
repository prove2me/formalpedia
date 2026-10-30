-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_04_scale_C1_of_true_esscher_cdf_continuous_local_density
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:01:58.663869+00:00
-- url     : https://prove2.me/submissions/d964189a-e667-45bc-90d7-fca89a4d02de

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal

/-- A genuine continuous local density of the all-real Esscher cumulative
scale law upgrades the scale function to positive-axis C1 regularity. -/
theorem solution
    (ν : Measure ℝ) (W : ℝ → ℝ) (φ m a : ℝ)
    (hm : 0 < m) (ha : 0 < a)
    (f : ℝ → ℝ) (hf : ContinuousOn f (Ioi (0 : ℝ)))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume a x)
    (hCDF : ∀ x : ℝ, 0 < x →
      W x = (Real.exp (φ * x) / m) * (ν (Iic x)).toReal)
    (hDensity : ∀ x : ℝ, 0 < x →
      (ν (Iic x)).toReal =
        (ν (Iic a)).toReal + ∫ t in a..x, f t) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
  let G : ℝ → ℝ := fun x => ∫ t in a..x, f t
  have hGderiv (x : ℝ) (hx : 0 < x) :
      HasDerivAt G (f x) x := by
    apply intervalIntegral.integral_hasDerivAt_right (hint x hx)
    · apply ContinuousAt.stronglyMeasurableAtFilter isOpen_Ioi
        (fun y hy => hf.continuousAt (isOpen_Ioi.mem_nhds hy))
      exact hx
    · exact hf.continuousAt (isOpen_Ioi.mem_nhds hx)
  have hGdiff : DifferentiableOn ℝ G (Ioi (0 : ℝ)) := by
    intro x hx
    exact (hGderiv x hx).differentiableAt.differentiableWithinAt
  have hGderivEq : EqOn (derivWithin G (Ioi (0 : ℝ)))
      f (Ioi (0 : ℝ)) := by
    intro x hx
    exact (hGderiv x hx).hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Ioi (0 : ℝ) x hx)
  have hGderivCont :
      ContinuousOn (derivWithin G (Ioi (0 : ℝ))) (Ioi (0 : ℝ)) :=
    hf.congr (fun x hx => hGderivEq hx)
  have hGC1 : ContDiffOn ℝ 1 G (Ioi (0 : ℝ)) :=
    (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioi (0 : ℝ))).2
      ⟨hGdiff, hGderivCont⟩
  have he : ContDiffOn ℝ 1
      (fun x : ℝ => Real.exp (φ * x) / m) (Ioi (0 : ℝ)) := by
    fun_prop
  have hc : ContDiffOn ℝ 1
      (fun x : ℝ => (ν (Iic a)).toReal + G x) (Ioi (0 : ℝ)) :=
    contDiffOn_const.add hGC1
  have hprod : ContDiffOn ℝ 1
      (fun x : ℝ => (Real.exp (φ * x) / m) *
        ((ν (Iic a)).toReal + G x)) (Ioi (0 : ℝ)) :=
    he.mul hc
  apply hprod.congr
  intro x hx
  simpa only [G, hDensity x hx] using hCDF x hx