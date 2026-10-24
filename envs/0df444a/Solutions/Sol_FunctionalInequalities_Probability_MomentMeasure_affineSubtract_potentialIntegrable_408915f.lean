-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.affineSubtract_potentialIntegrable_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:25:22.53958+00:00
-- url     : https://prove2.me/submissions/ac63acc2-9176-42d4-83e6-5210fb63e222

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

section
noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
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
end
end

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
section
open MeasureTheory
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
section StructuredSpace
variable [IsFiniteMeasure μ]
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
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
