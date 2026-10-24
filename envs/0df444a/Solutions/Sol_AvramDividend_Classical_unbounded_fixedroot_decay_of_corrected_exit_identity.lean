-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_fixedroot_decay_of_corrected_exit_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:04:09.200251+00:00
-- url     : https://prove2.me/submissions/bccdb1a7-baef-4d24-ada5-031cae008f9c

import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_scale_decay_of_corrected_exit_estimates
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-!
Combine the two published positive-root exit inequalities with canonical
unbounded-variation scale positivity. The only stochastic hypothesis left is
the killed two-sided exit identity itself.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-(φ * (y - x))) * W y := by
  have hpos : ∀ y : ℝ, 0 < y → 0 < W y :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  have hBound : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x ≤
        ENNReal.ofReal (Real.exp (-(φ * (a - x)))) := by
    intro a x ha hx hxa
    exact corrected_exit_exp_bound_at_positive_root
      X q hq φ hφ hroot a x ha hx hxa
  exact unbounded_fixedroot_scale_decay_of_corrected_exit_estimates
    X q W hpos φ hExit hBound
