-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.integral_affineSubtract_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:26:11.222797+00:00
-- url     : https://prove2.me/submissions/0d9930fa-acec-435b-a369-0886541078af

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
