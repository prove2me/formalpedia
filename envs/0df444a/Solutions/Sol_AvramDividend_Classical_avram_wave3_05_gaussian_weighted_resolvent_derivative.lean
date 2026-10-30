-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_gaussian_weighted_resolvent_derivative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:55:14.209981+00:00
-- url     : https://prove2.me/submissions/7afcee91-16d2-4e40-a5f5-26a2440d94b6

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- A signed Gaussian density yields a weighted L1 derivative at every sufficient discount. -/
theorem solution
    (g S : ℝ → ℝ) (a w θ : ℝ)
    (hθ : w ≤ θ)
    (hS : IntegrableOn S (Ioi (0 : ℝ)) volume)
    (hder : ∀ x : ℝ, 0 < x →
      HasDerivAt g (Real.exp (w * x) * (S x / a)) x) :
    IntegrableOn (fun x : ℝ => Real.exp (-(θ * x)) * deriv g x)
      (Ioi (0 : ℝ)) volume := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => Real.exp ((w - θ) * x)) μ :=
    ((continuous_const.mul continuous_id).rexp).aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ ∂μ,
      ‖Real.exp ((w - θ) * x)‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnonpos : (w - θ) * x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hθ) hx.le
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (Real.exp_le_one_iff.mpr hnonpos)
  have hweighted : IntegrableOn
      (fun x : ℝ => Real.exp ((w - θ) * x) * (S x / a))
      (Ioi (0 : ℝ)) volume :=
    (hS.div_const a).bdd_mul hmeas hbound
  have heq :
      (fun x : ℝ => Real.exp (-(θ * x)) * deriv g x) =ᵐ[μ]
      (fun x : ℝ => Real.exp ((w - θ) * x) * (S x / a)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [(hder x hx).deriv]
    calc
      Real.exp (-(θ * x)) * (Real.exp (w * x) * (S x / a)) =
          (Real.exp (-(θ * x)) * Real.exp (w * x)) * (S x / a) := by ring
      _ = Real.exp ((w - θ) * x) * (S x / a) := by
        rw [← Real.exp_add]
        congr 1
        ring
  exact hweighted.congr heq.symm
