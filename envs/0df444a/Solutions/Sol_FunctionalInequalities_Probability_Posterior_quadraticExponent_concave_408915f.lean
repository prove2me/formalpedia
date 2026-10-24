-- Prove2me | solution 1 for FunctionalInequalities.Probability.Posterior.quadraticExponent_concave_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:06:52.930152+00:00
-- url     : https://prove2.me/submissions/5c45066d-3601-4aad-b9cf-b998c3c80abf

import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Posterior_Exponent
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.Posterior
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace FunctionalInequalities.Probability.Posterior
end FunctionalInequalities.Probability.Posterior
open FunctionalInequalities.Probability.Posterior in
open Set in
/-- The exponent `⟪c,x⟫ − ½⟪Qx,x⟫` is concave for symmetric nonnegative `Q`. -/
theorem solution (c : E) (Q : E →L[ℝ] E)
    (hSym : ∀ u v : E, ⟪Q u, v⟫ = ⟪u, Q v⟫)
    (hQ : ∀ x : E, 0 ≤ ⟪Q x, x⟫) : ConcaveOn ℝ univ (FunctionalInequalities.Probability.Posterior.quadraticExponent c Q) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hcross : ⟪Q y, x⟫ = ⟪Q x, y⟫ := by
    rw [hSym y x, real_inner_comm]
  have hdiff : 0 ≤ ⟪Q x, x⟫ - 2 * ⟪Q x, y⟫ + ⟪Q y, y⟫ := by
    have h := hQ (x - y)
    simp only [map_sub, inner_sub_left, inner_sub_right] at h
    rw [hcross] at h
    linarith
  have he : FunctionalInequalities.Probability.Posterior.quadraticExponent c Q (a • x + b • y) -
      (a * FunctionalInequalities.Probability.Posterior.quadraticExponent c Q x + b * FunctionalInequalities.Probability.Posterior.quadraticExponent c Q y) =
      (a * b / 2) * (⟪Q x, x⟫ - 2 * ⟪Q x, y⟫ + ⟪Q y, y⟫) := by
    obtain rfl : b = 1 - a := by linarith
    simp only [FunctionalInequalities.Probability.Posterior.quadraticExponent, map_add, map_smul, inner_add_left, inner_add_right,
      real_inner_smul_left, inner_smul_right]
    rw [hcross]
    ring
  have hh := mul_nonneg (div_nonneg (mul_nonneg ha hb) (by norm_num : (0 : ℝ) ≤ 2)) hdiff
  simp only [smul_eq_mul]
  linarith
