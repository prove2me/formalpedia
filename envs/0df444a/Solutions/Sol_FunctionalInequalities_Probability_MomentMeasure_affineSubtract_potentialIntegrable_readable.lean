-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.affineSubtract_potentialIntegrable_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:18.992003+00:00
-- url     : https://prove2.me/submissions/5853a51e-795d-4d25-a462-eabea6c58707

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
/-- The actual affine perturbation is admissible under the input first moment.
Neither output integrability nor a supporting affine plane is assumed. -/
theorem solution
    (f : E → EReal) (a : E) (b : ℝ) (hf : FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f μ)
    (hfirst : Integrable (fun x : E => x) μ) :
    FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable (FunctionalInequalities.Analysis.affineSubtract f a b) μ := by
  have hlin : Integrable (fun x => inner ℝ a x) μ := (innerSL ℝ a).integrable_comp hfirst
  have heq : (fun x => (FunctionalInequalities.Analysis.affineSubtract f a b x).toReal) =ᵐ[μ]
      (fun x => (f x).toReal - (inner ℝ a x + b)) := by
    filter_upwards [hf.2.1] with x hx
    exact FunctionalInequalities.Analysis.affineSubtract_toReal_of_finite f a b x hx (hf.1 x)
  refine ⟨?_, ?_, ?_⟩
  · intro x
    change f x - ((inner ℝ a x + b : ℝ) : EReal) ≠ ⊥
    by_cases ht : f x = ⊤
    · rw [ht, EReal.top_sub_coe]
      exact top_ne_bot
    · rw [← EReal.coe_toReal ht (hf.1 x), ← EReal.coe_sub]
      exact EReal.coe_ne_bot _
  · filter_upwards [hf.2.1] with x hx
    change f x - ((inner ℝ a x + b : ℝ) : EReal) ≠ ⊤
    rw [← EReal.coe_toReal hx (hf.1 x), ← EReal.coe_sub]
    exact EReal.coe_ne_top _
  · exact (hf.2.2.sub (hlin.add (integrable_const b))).congr (Filter.EventuallyEq.symm heq)
