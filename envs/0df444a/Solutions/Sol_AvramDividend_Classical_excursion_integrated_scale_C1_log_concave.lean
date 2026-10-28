-- Prove2me | solution 1 for AvramDividend.Classical.excursion_integrated_scale_C1_log_concave
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:57:08.414491+00:00
-- url     : https://prove2.me/submissions/925e3491-07eb-411e-9963-9ae1d673d6e4

import Theorems.Thm_AvramDividend_Classical_excursion_integral_scale_derivative
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_of_deriv_eq_continuous_product_Ioi
import Theorems.Thm_AvramDividend_Classical_excursion_log_concave_of_derivative_representation
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set intervalIntegral

theorem solution
    (W : ℝ → ℝ) (φ : ℝ) (μ : Measure ℝ)
    (hcont : ContinuousOn (fun t : ℝ => μ.real (Ici t)) (Ioi (0 : ℝ)))
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤)
    (hWpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hexp : ∀ a b : ℝ, 0 < a → a ≤ b →
      W b = W a * Real.exp (∫ t in a..b, φ + μ.real (Ici t))) :
    ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) ∧
      ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (W x)) := by
  have hderiv := excursion_integral_scale_derivative W φ μ hcont hexp
  have hg : ContinuousOn
      (fun x : ℝ => φ + μ.real (Ici x)) (Ioi (0 : ℝ)) := by
    exact continuousOn_const.add hcont
  have hWdiff : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)) := by
    apply contDiffOn_one_of_deriv_eq_continuous_product_Ioi
      W (fun x : ℝ => φ + μ.real (Ici x)) hg
    intro x hx
    simpa only [mul_comm] using hderiv x hx
  have hpoint : ∀ x : ℝ, 0 < x →
      HasDerivAt W (deriv W x) x := by
    intro x hx
    simpa only [(hderiv x hx).deriv] using hderiv x hx
  have hderiv_eq : ∀ x : ℝ, 0 < x →
      deriv W x = W x * (φ + μ.real (Ici x)) := by
    intro x hx
    exact (hderiv x hx).deriv
  exact ⟨hWdiff,
    excursion_log_concave_of_derivative_representation
      W μ φ hfin hWpos hderiv_eq hpoint⟩
