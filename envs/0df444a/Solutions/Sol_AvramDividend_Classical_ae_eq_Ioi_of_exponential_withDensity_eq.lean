-- Prove2me | solution 1 for AvramDividend.Classical.ae_eq_Ioi_of_exponential_withDensity_eq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T22:11:19.982389+00:00
-- url     : https://prove2.me/submissions/90feb672-263f-440b-9750-2d80ad706b1f

import Mathlib

open MeasureTheory Filter Set Topology
open scoped ENNReal

theorem solution
    (f g : ℝ → ℝ) (B : ℝ)
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
    f =ᵐ[volume.restrict (Ioi 0)] g := by
  have hdens :
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * f x)) =ᵐ[
        volume.restrict (Ioi 0)]
      (fun x : ℝ => ENNReal.ofReal (Real.exp (-B * x) * g x)) :=
    (withDensity_eq_iff_of_sigmaFinite hfdens hgdens).mp hmeas
  filter_upwards [hdens, ae_restrict_mem measurableSet_Ioi] with x hx hpos
  have hef : 0 ≤ Real.exp (-B * x) * f x :=
    mul_nonneg (Real.exp_pos _).le (hfnonneg x hpos)
  have heg : 0 ≤ Real.exp (-B * x) * g x :=
    mul_nonneg (Real.exp_pos _).le (hgnonneg x hpos)
  have hprod : Real.exp (-B * x) * f x = Real.exp (-B * x) * g x :=
    (ENNReal.ofReal_eq_ofReal_iff hef heg).mp hx
  exact mul_left_cancel₀ (Real.exp_ne_zero (-B * x)) hprod
