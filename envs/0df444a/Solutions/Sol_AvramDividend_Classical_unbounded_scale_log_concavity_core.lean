-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_scale_log_concavity_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T11:12:20.659302+00:00
-- url     : https://prove2.me/submissions/599dbdcc-4924-47ba-8d61-f696c05d67cb

import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_infinite_variation_without_standing
import Theorems.Thm_AvramDividend_Classical_unbounded_corrected_exit_scale_identity
import Theorems.Thm_AvramDividend_Classical_unbounded_tilted_scale_log_concavity_of_corrected_exit
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Genuine original q-scale log-concavity from corrected upward-exit probabilities
and Standing-free C1 smoothing in the Gaussian and infinite-jump-variation cases. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ConcaveOn ℝ (Set.Ioi (0 : ℝ)) (fun x : ℝ => Real.log (W x)) := by
  have hC1 : ContDiffOn ℝ 1 W (Set.Ioi (0 : ℝ)) := by
    by_cases hσ : 0 < X.σ
    · exact scaleFunction_contDiff_one_gaussian_without_standing
        X q hq W hW hσ
    · have hσzero : X.σ = 0 :=
        le_antisymm (le_of_not_gt hσ) X.σ_nonneg
      have hvar :
          ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν = ⊤ := by
        by_contra hnot
        have hfinite :
            ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν < ⊤ :=
          lt_top_iff_ne_top.mpr hnot
        exact hnbv ⟨hσzero, hfinite⟩
      exact scaleFunction_contDiff_one_infinite_variation_without_standing
        X q hq W hW hvar
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    have hpoint : ContDiffAt ℝ 1 W x :=
      hC1.contDiffAt (isOpen_Ioi.mem_nhds hx)
    exact hpoint.differentiableAt (by norm_num)
  have hExit :
      ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
        twoSidedExitExpectationCorrected X q a x =
          ENNReal.ofReal (W x / W a) := by
    intro a x ha hx hxa
    exact unbounded_corrected_exit_scale_identity
      X q hq W hW hnbv a x ha hx.le hxa
  have htilted :=
    unbounded_tilted_scale_log_concavity_of_corrected_exit
      X q hq W hW hnbv hExit 0 hdiff
  simpa only [zero_mul, neg_zero, Real.exp_zero, one_mul] using htilted
