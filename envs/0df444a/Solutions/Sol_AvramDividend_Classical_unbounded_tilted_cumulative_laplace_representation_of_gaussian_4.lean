-- Prove2me | solution 4 for AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:41:33.664967+00:00
-- url     : https://prove2.me/submissions/15682df6-a97e-4a7f-97e7-57899f1edac7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_cumulative_laplace_representation_of_corrected_exit
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

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
  -- Route: Proved 21a19c48 gives the exact cumulative representation from
  -- (Standing + ¬BV + hExit). Derive ¬BV from Gaussian 0 < σ (BV needs σ = 0),
  -- supply hExit pointwise from Open 6d3911f8 with verbatim binders.
  have hnbv : ¬ X.BoundedVariation := by
    intro hBV
    obtain ⟨hσ0, _⟩ := hBV
    linarith
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) :=
    fun a x ha hx hxa =>
      AvramDividend.Classical.unbounded_corrected_exit_scale_identity
        X q hq W hW hnbv a x ha hx hxa
  exact AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_corrected_exit
    X hX q hq W hW hnbv hExit