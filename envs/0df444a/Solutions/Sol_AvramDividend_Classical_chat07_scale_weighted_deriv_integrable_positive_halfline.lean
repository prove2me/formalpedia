-- Prove2me | solution 1 for AvramDividend.Classical.chat07_scale_weighted_deriv_integrable_positive_halfline
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T06:30:41.262855+00:00
-- url     : https://prove2.me/submissions/cf3fb697-523a-42ec-a723-71b825f20e7e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_monotone
import Theorems.Thm_AvramDividend_Classical_scaleFunction_shiftedLaplace_integrable
import Theorems.Thm_AvramDividend_Classical_chat07_scale_deriv_interval_integrable_and_mass_bound
import Theorems.Thm_AvramDividend_Classical_chat07_scale_weighted_deriv_adjacent_unit_intervals
import Theorems.Thm_AvramDividend_Classical_chat07_adjacent_interval_integral_bound_fin
import Theorems.Thm_AvramDividend_Classical_chat07_finite_nonnegative_interval_integral_le_positive_halfline
import Theorems.Thm_AvramDividend_Classical_chat07_integrableOn_positive_halfline_of_uniform_interval_abs_bound
import Mathlib.Analysis.Calculus.Deriv.Slope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal
open AvramDividend.Classical
/-! Exponential scale-derivative integrability via adjacent interval bounds. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (θ : ℝ) (hθ : 0 ≤ θ) (hqθ : q < X.ψ θ) :
    IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * deriv W x)
      (Ioi (0 : ℝ)) := by
  let f : ℝ → ℝ := fun x => Real.exp (-(θ * x)) * deriv W x
  let g : ℝ → ℝ := fun x => Real.exp (-(θ * x)) * W x
  have hm : Monotone W := scaleFunction_monotone X q W hW
  have hc : Continuous (fun x : ℝ => Real.exp (-(θ * x))) :=
    Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg)
  have hf : ∀ a b : ℝ, IntervalIntegrable f volume a b := by
    intro a b
    exact (chat07_scale_deriv_interval_integrable_and_mass_bound
      X q W hW a b).1.continuousOn_mul hc.continuousOn
  have hg : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
    intro a b
    exact (hm.intervalIntegrable).continuousOn_mul hc.continuousOn
  have hfnonneg : ∀ x : ℝ, 0 ≤ f x := by
    intro x
    exact mul_nonneg (Real.exp_pos _).le (hm.deriv_nonneg)
  have hgnonneg : ∀ x : ℝ, 0 ≤ g x := by
    intro x
    have hWx : 0 ≤ W x := by
      by_cases hx : x < 0
      · rw [hW.1 x hx]
      · exact hW.2.1 x (le_of_not_gt hx)
    exact mul_nonneg (Real.exp_pos _).le hWx
  have hgGlobal : IntegrableOn g (Ioi (0 : ℝ)) := by
    simpa only [g, add_zero] using
      (scaleFunction_shiftedLaplace_integrable
        X q W hW θ 0 hθ hqθ le_rfl)
  have hstep : ∀ n : ℕ,
      (∫ x in (n : ℝ)..((n : ℝ) + 1), f x) ≤
        Real.exp (2 * θ) *
          (∫ x in ((n : ℝ) + 1)..((n : ℝ) + 2), g x) := by
    intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    simpa only [f, g] using
      (chat07_scale_weighted_deriv_adjacent_unit_intervals
        X q W hW θ (n : ℝ) hθ hn (hW.2.1 (n : ℝ) hn))
  have hbound : ∀ n : ℕ,
      (∫ x in (0 : ℝ)..(n : ℝ), |f x|) ≤
        Real.exp (2 * θ) * (∫ x in Ioi (0 : ℝ), g x) := by
    intro n
    calc
      (∫ x in (0 : ℝ)..(n : ℝ), |f x|) =
          (∫ x in (0 : ℝ)..(n : ℝ), f x) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact abs_of_nonneg (hfnonneg x)
      _ ≤ Real.exp (2 * θ) *
          (∫ x in (1 : ℝ)..((n : ℝ) + 1), g x) :=
        chat07_adjacent_interval_integral_bound_fin
          f g (Real.exp (2 * θ)) hf hg hstep n
      _ ≤ Real.exp (2 * θ) *
          (∫ x in Ioi (0 : ℝ), g x) :=
        mul_le_mul_of_nonneg_left
          (chat07_finite_nonnegative_interval_integral_le_positive_halfline
            g hgGlobal hgnonneg n) (Real.exp_pos _).le
  exact chat07_integrableOn_positive_halfline_of_uniform_interval_abs_bound
    f (Real.exp (2 * θ) * (∫ x in Ioi (0 : ℝ), g x))
    (fun n => hf 0 (n : ℝ)) hbound
