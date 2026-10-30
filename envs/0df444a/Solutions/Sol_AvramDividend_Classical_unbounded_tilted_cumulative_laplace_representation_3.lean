-- Prove2me | solution 3 for AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T18:12:29.778843+00:00
-- url     : https://prove2.me/submissions/48706b4b-27c0-4e4b-952c-46ce9eb7bc67

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_tilt_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_positive_esscher_shift_laplace_domain
import Theorems.Thm_AvramDividend_Classical_esscher_cumulative_laplace_of_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! General unbounded-variation cumulative Laplace law via corrected exit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
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
  have hvar0 : X.σ = 0 →
      (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ := by
    intro hs0
    rcases unbounded_variation_gaussian_or_infinite_small_jump_moment
      X hnbv with hσ | hvar
    · exact False.elim ((ne_of_gt hσ) hs0)
    · exact hvar
  have hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a x ha hx hxa
  obtain ⟨hpos, φ, hφ, hroot, htilt⟩ :=
    unbounded_positive_tilt_of_corrected_exit
      X q hq W hW hnbv hExit
  have hzero : W 0 = 0 := by
    by_cases hs : 0 < X.σ
    · exact scaleFunction_zero_origin_gaussian_without_standing
        X q hq W hW hs
    · have hs0 : X.σ = 0 :=
        le_antisymm (le_of_not_gt hs) X.σ_nonneg
      exact scaleFunction_zero_origin_infinite_small_jumps
        X hs0 (hvar0 hs0) q hq W hW
  have hcut : ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      0 ≤ θ + φ ∧ q < X.ψ (θ + φ) := by
    by_cases hs : 0 < X.σ
    · obtain ⟨β₀, _, hψ⟩ := psi_eventually_gt_of_gaussian X q hs
      exact positive_esscher_shift_laplace_domain X.ψ q φ β₀ hφ hψ
    · have hs0 : X.σ = 0 :=
        le_antisymm (le_of_not_gt hs) X.σ_nonneg
      obtain ⟨β₀, _, hψ⟩ :=
        psi_eventually_gt_of_infinite_small_jump_moment
          X hs0 (hvar0 hs0) q hq
      exact positive_esscher_shift_laplace_domain X.ψ q φ β₀ hφ hψ
  exact esscher_cumulative_laplace_of_monotone
    X q W hW hzero φ hφ hpos
      (by simpa only [neg_mul] using htilt) hcut
