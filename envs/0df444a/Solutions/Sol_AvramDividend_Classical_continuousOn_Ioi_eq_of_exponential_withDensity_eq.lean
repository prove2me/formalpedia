-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_Ioi_eq_of_exponential_withDensity_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T20:52:36.759461+00:00
-- url     : https://prove2.me/submissions/9bf43c7f-538b-4aea-87aa-a55cc273a7a0

import Mathlib

open MeasureTheory Filter Set Topology
open scoped MeasureTheory ProbabilityTheory ENNReal NNReal Topology

theorem solution
    (f g : ℝ → ℝ) (B : ℝ)
    (hfcont : ContinuousOn f (Ioi 0))
    (hgcont : ContinuousOn g (Ioi 0))
    (hfnonneg : ∀ x : ℝ, 0 < x → 0 ≤ f x)
    (hgnonneg : ∀ x : ℝ, 0 < x → 0 ≤ g x)
    (hfdens : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * f x))
      (volume.restrict (Ioi 0)))
    (hgdens : AEMeasurable
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * g x))
      (volume.restrict (Ioi 0)))
    (hmeas :
      (volume.restrict (Ioi 0)).withDensity
          (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * f x)) =
        (volume.restrict (Ioi 0)).withDensity
          (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * g x))) :
    ∀ x : ℝ, 0 < x → f x = g x := by
  have hdens :
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * f x)) =ᵐ[
        volume.restrict (Ioi 0)]
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * g x)) :=
    (withDensity_eq_iff_of_sigmaFinite hfdens hgdens).mp hmeas
  have hfg : f =ᵐ[volume.restrict (Ioi 0)] g := by
    filter_upwards [hdens, ae_restrict_mem measurableSet_Ioi] with x hx hpos
    have hef : 0 ≤ Real.exp (-B * x) * f x :=
      mul_nonneg (Real.exp_pos _).le (hfnonneg x hpos)
    have heg : 0 ≤ Real.exp (-B * x) * g x :=
      mul_nonneg (Real.exp_pos _).le (hgnonneg x hpos)
    have hprod : Real.exp (-B * x) * f x = Real.exp (-B * x) * g x :=
      (ENNReal.ofReal_eq_ofReal_iff hef heg).mp hx
    exact mul_left_cancel₀ (Real.exp_ne_zero (-B * x)) hprod
  have hEqOn : EqOn f g (Ioi 0) :=
    MeasureTheory.Measure.eqOn_open_of_ae_eq hfg isOpen_Ioi hfcont hgcont
  intro x hx
  exact hEqOn hx
