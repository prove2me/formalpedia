-- Prove2me | solution 3 for AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T17:54:22.369801+00:00
-- url     : https://prove2.me/submissions/40d72202-dced-4c03-9ed2-bf96f6426b0d

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_fixedroot_decay_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_gaussian_cumulative_of_exit_decay_without_aux
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! The Gaussian tilted cumulative Laplace law follows from corrected exit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x) =
          ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
            (β (Iic x)).toReal := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hbv
    exact (ne_of_gt hσ) hbv.1
  apply gaussian_cumulative_of_exit_decay_without_aux X q hq W hW hσ
  intro φ hφ hroot x y hx hxy
  have hExit : ∀ a z : ℝ, 0 < a → 0 ≤ z → z ≤ a →
      twoSidedExitExpectationCorrected X q a z =
        ENNReal.ofReal (W z / W a) := by
    intro a z ha hz hza
    exact unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a z ha hz hza
  simpa only [neg_mul] using
    (unbounded_fixedroot_decay_of_corrected_exit_identity
      X q hq W hW hnbv φ hφ hroot hExit x y hx hxy)
