-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_infinite_small_jump
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T15:47:42.116798+00:00
-- url     : https://prove2.me/submissions/e117c02c-488a-442a-a1cb-a4ce466f6553
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_zero_origin_infinite_small_jumps
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_gaussian
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_positive_esscher_shift_laplace_domain
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_first_passage_scale_decay
import Theorems.Thm_AvramDividend_Classical_exit_decay_implies_tilted_monotone
import Theorems.Thm_AvramDividend_Classical_esscher_cumulative_laplace_of_monotone
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-! Positive-root decay yields the infinite-jump cumulative Laplace law. -/
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
  have hnbv : ¬ X.BoundedVariation := by
    intro hbv
    exact (ne_of_lt hbv.2) hvar
  have hpos : ∀ x : ℝ, 0 < x → 0 < W x :=
    scaleFunction_strict_pos_of_unbounded_variation X q W hW hnbv
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hnbv q hq
  have hdecay :=
    unbounded_esscher_root_first_passage_scale_decay
      X q hq W hW hnbv φ hφ hroot
  have htilt : MonotoneOn
      (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) :=
    exit_decay_implies_tilted_monotone W φ
      (by simpa only [neg_mul] using hdecay)
  have hzero : W 0 = 0 := by
    by_cases hs : 0 < X.σ
    · exact scaleFunction_zero_origin_gaussian_without_standing
        X q hq W hW hs
    · have hs0 : X.σ = 0 :=
        le_antisymm (le_of_not_gt hs) X.σ_nonneg
      exact scaleFunction_zero_origin_infinite_small_jumps
        X hs0 hvar q hq W hW
  have hcut : ∃ b : ℝ, ∀ θ : ℝ, b < θ →
      0 ≤ θ + φ ∧ q < X.ψ (θ + φ) := by
    by_cases hs : 0 < X.σ
    · obtain ⟨β₀, _, hψ⟩ := psi_eventually_gt_of_gaussian X q hs
      exact positive_esscher_shift_laplace_domain X.ψ q φ β₀ hφ hψ
    · have hs0 : X.σ = 0 :=
        le_antisymm (le_of_not_gt hs) X.σ_nonneg
      obtain ⟨β₀, _, hψ⟩ :=
        psi_eventually_gt_of_infinite_small_jump_moment X hs0 hvar q hq
      exact positive_esscher_shift_laplace_domain X.ψ q φ β₀ hφ hψ
  exact esscher_cumulative_laplace_of_monotone
    X q W hW hzero φ hφ hpos htilt hcut
