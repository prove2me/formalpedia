-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.integral_affineSubtract_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:20.150579+00:00
-- url     : https://prove2.me/submissions/17844c9b-c5e0-43e2-a91b-c0883269c7d4

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Affine

section
noncomputable section
section
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- At every finite input point the actual affine perturbation has its intended
real restriction; no global finiteness is assumed. -/
theorem FunctionalInequalities.Analysis.affineSubtract_toReal_of_finite (f : E → EReal) (a : E) (b : ℝ) (x : E)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    (affineSubtract f a b x).toReal = (f x).toReal - (inner ℝ a x + b) := by
  exact EReal.toReal_sub ht hb (EReal.coe_ne_top _) (EReal.coe_ne_bot _)
end
end
end

noncomputable section
open FunctionalInequalities.Analysis
section
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E}
section StructuredSpace
variable [MeasureTheory.IsFiniteMeasure μ]
omit [BorelSpace E] in
/-- The actual integral formula retains total mass for a general finite measure.
This is not asserted to be invariant under a constant shift at arbitrary mass. -/
theorem solution
    (f : E → EReal) (a : E) (b : ℝ) (hf : FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) :
    (∫ x, (FunctionalInequalities.Analysis.affineSubtract f a b x).toReal ∂μ) =
      (∫ x, (f x).toReal ∂μ) - (∫ x, inner ℝ a x ∂μ) - (μ Set.univ).toReal * b := by
  have hlin : Integrable (fun x => inner ℝ a x) μ := (innerSL ℝ a).integrable_comp hfirst
  have heq : (fun x => (FunctionalInequalities.Analysis.affineSubtract f a b x).toReal) =ᵐ[μ]
      (fun x => (f x).toReal - (inner ℝ a x + b)) := by
    filter_upwards [hf.2.1] with x hx
    exact FunctionalInequalities.Analysis.affineSubtract_toReal_of_finite f a b x hx (hf.1 x)
  have hAff : Integrable (fun x => inner ℝ a x + b) μ := hlin.add (integrable_const b)
  have hsub : (∫ x, (f x).toReal - (inner ℝ a x + b) ∂μ) =
      (∫ x, (f x).toReal ∂μ) - ∫ x, inner ℝ a x + b ∂μ := integral_sub hf.2.2 hAff
  have hadd : (∫ x, inner ℝ a x + b ∂μ) = (∫ x, inner ℝ a x ∂μ) + ∫ _ : E, b ∂μ :=
    integral_add hlin (integrable_const b)
  rw [integral_congr_ae heq, hsub, hadd, integral_const]
  simp only [smul_eq_mul, measureReal_def]
  ring
