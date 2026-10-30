-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_05_second_deriv_weighted_from_signed
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T00:55:19.301329+00:00
-- url     : https://prove2.me/submissions/8760b610-4786-47ae-9b7f-94d4e234ca1a

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- The source Esscher second derivative has weighted L1 under proven first-order bounds. -/
theorem solution
    (W S : ℝ → ℝ) (φ w θ a : ℝ)
    (hθ : φ + w ≤ θ)
    (hW : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * W x) (Ioi (0 : ℝ)) volume)
    (hWder : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * deriv W x)
      (Ioi (0 : ℝ)) volume)
    (hS : IntegrableOn S (Ioi (0 : ℝ)) volume)
    (hsecond : ∀ x : ℝ, 0 < x →
      deriv (deriv W) x =
        2 * φ * deriv W x - φ ^ 2 * W x +
          Real.exp ((φ + w) * x) * (S x / a)) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * deriv (deriv W) x)
      (Ioi (0 : ℝ)) volume := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => Real.exp (((φ + w) - θ) * x)) μ :=
    ((continuous_const.mul continuous_id).rexp).aestronglyMeasurable
  have hbound : ∀ᵐ x : ℝ ∂μ,
      ‖Real.exp (((φ + w) - θ) * x)‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hnonpos : ((φ + w) - θ) * x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hθ) hx.le
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      (Real.exp_le_one_iff.mpr hnonpos)
  have hweighted : IntegrableOn
      (fun x : ℝ => Real.exp (((φ + w) - θ) * x) * (S x / a))
      (Ioi (0 : ℝ)) volume :=
    (hS.div_const a).bdd_mul hmeas hbound
  have hsum : IntegrableOn (fun x : ℝ =>
      (2 * φ) * (Real.exp (-(θ * x)) * deriv W x) -
        φ ^ 2 * (Real.exp (-(θ * x)) * W x) +
        Real.exp (((φ + w) - θ) * x) * (S x / a))
      (Ioi (0 : ℝ)) volume :=
    ((hWder.const_mul (2 * φ)).sub (hW.const_mul (φ ^ 2))).add hweighted
  have heq :
      (fun x : ℝ => Real.exp (-(θ * x)) * deriv (deriv W) x) =ᵐ[μ]
      (fun x : ℝ =>
        (2 * φ) * (Real.exp (-(θ * x)) * deriv W x) -
          φ ^ 2 * (Real.exp (-(θ * x)) * W x) +
          Real.exp (((φ + w) - θ) * x) * (S x / a)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [hsecond x hx]
    calc
      Real.exp (-(θ * x)) *
          (2 * φ * deriv W x - φ ^ 2 * W x +
            Real.exp ((φ + w) * x) * (S x / a)) =
          (2 * φ) * (Real.exp (-(θ * x)) * deriv W x) -
            φ ^ 2 * (Real.exp (-(θ * x)) * W x) +
            (Real.exp (-(θ * x)) * Real.exp ((φ + w) * x)) *
              (S x / a) := by ring
      _ = (2 * φ) * (Real.exp (-(θ * x)) * deriv W x) -
            φ ^ 2 * (Real.exp (-(θ * x)) * W x) +
            Real.exp (((φ + w) - θ) * x) * (S x / a) := by
        rw [← Real.exp_add]
        congr 1
        ring
  exact hsum.congr heq.symm
