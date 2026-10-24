-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.real_legendre_normalization_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:29:32.683036+00:00
-- url     : https://prove2.me/submissions/2d442848-7aad-4f19-aaf0-5140ad8b59b3

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.LiminfLimsup
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- Every affine summand of the actual extended-real conjugate is continuous,
including when its fixed intercept is an infinite value. -/
theorem FunctionalInequalities.Analysis.continuous_legendre_summand (φ : E → EReal) (x : E) :
    Continuous (fun y : E => (inner ℝ x y : EReal) - φ x) := by
  by_cases hb : φ x = ⊥
  · simpa only [hb, EReal.coe_sub_bot] using
      (continuous_const : Continuous (fun _ : E => (⊤ : EReal)))
  by_cases ht : φ x = ⊤
  · simpa only [ht, EReal.sub_top] using
      (continuous_const : Continuous (fun _ : E => (⊥ : EReal)))
  lift φ x to ℝ using ⟨ht, hb⟩ with r hr
  have hc : Continuous (fun y : E => inner ℝ x y - r) :=
    (continuous_const.inner continuous_id).sub continuous_const
  simpa only [Function.comp_def, ← hr, ← EReal.coe_sub] using continuous_coe_real_ereal.comp hc
/-- The conjugate is lower semicontinuous for any extended-real input;
no properness, convexity, finite dimension or global finiteness is required. -/
theorem FunctionalInequalities.Analysis.lowerSemicontinuous_legendre (φ : E → EReal) :
    LowerSemicontinuous (legendre φ) := by
  exact lowerSemicontinuous_iSup (fun x =>
    (continuous_legendre_summand φ x).lowerSemicontinuous)
end
end
end
end

section
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
open MeasureTheory
open scoped ENNReal
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
/-- The density of the actual conjugate is Borel even for a nonmeasurable primal. -/
theorem FunctionalInequalities.Probability.MomentMeasure.measurable_density_legendre [MeasurableSpace E] [BorelSpace E] (φ : E → EReal) :
    Measurable (density (legendre φ)) :=
  EReal.measurable_exp.comp (lowerSemicontinuous_legendre φ).measurable.neg
end
end
end
end
end

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology
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
section RealNormalization
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
omit [FiniteDimensional ℝ E] in
/-- Actual conjugate mass one gives genuine Bochner integrability and a
probability measure for its finite real representative. Integral finiteness
is established before using the ENNReal-to-real integrability bridge. -/
theorem solution
    (dx : Measure E) (q : E → EReal) (ψ : E → ℝ)
    (hψ : ∀ x, FunctionalInequalities.Analysis.legendre q x = (ψ x : EReal))
    (hmass : FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre q) = 1) :
    Integrable (fun x => Real.exp (-ψ x)) dx ∧
    (∫ x, Real.exp (-ψ x) ∂dx) = 1 ∧
    IsProbabilityMeasure (FunctionalInequalities.Probability.MomentMeasure.weightedMeasure dx (fun x => (ψ x : EReal))) := by
  have hd : FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre q) =
      (fun x => ENNReal.ofReal (Real.exp (-ψ x))) := by
    funext x
    simp only [FunctionalInequalities.Probability.MomentMeasure.density, hψ x, ← EReal.coe_neg, EReal.exp_coe]
  have hmassfinite : (∫⁻ x, FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre q) x ∂dx) ≠ ∞ := by
    change FunctionalInequalities.Probability.MomentMeasure.mass dx (FunctionalInequalities.Analysis.legendre q) ≠ ∞
    rw [hmass]
    exact ENNReal.one_ne_top
  have hi : Integrable (fun x => (FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre q) x).toReal) dx :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top
      (FunctionalInequalities.Probability.MomentMeasure.measurable_density_legendre q).aemeasurable hmassfinite
  have hreal : (fun x => (FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre q) x).toReal) =
      (fun x => Real.exp (-ψ x)) := by
    funext x
    rw [hd, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  rw [hreal] at hi
  have hmass' : (∫⁻ x, ENNReal.ofReal (Real.exp (-ψ x)) ∂dx) = 1 := by
    simpa only [FunctionalInequalities.Probability.MomentMeasure.mass, hd] using hmass
  have hnonneg : ∀ᵐ x ∂dx, 0 ≤ Real.exp (-ψ x) :=
    Filter.Eventually.of_forall (fun x => Real.exp_nonneg (-ψ x))
  have hpotential : (fun x : E => (ψ x : EReal)) = FunctionalInequalities.Analysis.legendre q :=
    funext (fun x => (hψ x).symm)
  refine ⟨hi, ?_, ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae hnonneg hi.aestronglyMeasurable,
      hmass', ENNReal.toReal_one]
  · constructor
    change (dx.withDensity (FunctionalInequalities.Probability.MomentMeasure.density (fun x => (ψ x : EReal)))) univ = 1
    rw [hpotential, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ]
    exact hmass
