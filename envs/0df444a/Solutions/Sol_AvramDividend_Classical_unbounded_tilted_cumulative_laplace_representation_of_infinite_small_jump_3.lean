-- Prove2me | solution 3 for AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_infinite_small_jump
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-28T10:44:47.9+00:00
-- url     : https://prove2.me/submissions/dde67d75-680b-4166-a3c7-0e86d4a8f821
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

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
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤) :
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
  -- (Standing + ¬BV + hExit). Derive ¬BV from infinite small-jump first moment
  -- (BV needs that lintegral < top), supply hExit pointwise from Open 6d3911f8.
  have hnbv : ¬ X.BoundedVariation := by
    intro hBV
    obtain ⟨_, hfin⟩ := hBV
    rw [hvar] at hfin
    exact (lt_irrefl _ hfin).elim
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) :=
    fun a x ha hx hxa =>
      AvramDividend.Classical.unbounded_corrected_exit_scale_identity
        X q hq W hW hnbv a x ha hx hxa
  exact AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_corrected_exit
    X hX q hq W hW hnbv hExit