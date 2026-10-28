-- Prove2me | solution 1 for AvramDividend.Classical.excursion_log_concave_of_derivative_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T13:36:41.676408+00:00
-- url     : https://prove2.me/submissions/388e53ad-0065-4fc8-9a08-04f8a091166c

import Theorems.Thm_AvramDividend_Classical_excursion_log_derivative_antitoneOn
import Theorems.Thm_AvramDividend_Classical_concave_log_of_antitone_log_derivative
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

theorem solution
    (W : ℝ → ℝ) (μ : Measure ℝ) (φ : ℝ)
    (hfin : ∀ x : ℝ, 0 < x → μ (Ici x) ≠ ⊤)
    (hWpos : ∀ x : ℝ, 0 < x → 0 < W x)
    (hderiv : ∀ x : ℝ, 0 < x →
      deriv W x = W x * (φ + μ.real (Ici x)))
    (hWdiff : ∀ x : ℝ, 0 < x → HasDerivAt W (deriv W x) x) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun x : ℝ => Real.log (W x)) := by
  exact concave_log_of_antitone_log_derivative W hWpos hWdiff
    (excursion_log_derivative_antitoneOn W μ φ hfin hWpos hderiv)
