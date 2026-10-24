-- Prove2me | solution 1 for FunctionalInequalities.KLS.CEK.exists_uniform_functional_upper_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:40:59.094983+00:00
-- url     : https://prove2.me/submissions/0fe3dfd6-aa16-431d-9e13-8378bcd66d70

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_KLS_CEK_exists_normalized_competitor_408915f
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_coercivity_of_centered_probability_408915f
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_real_coercivity_le_uniform_408915f

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
open FunctionalInequalities.Analysis
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
section Integral
variable {E : Type*} [MeasurableSpace E] {μ : Measure E}
/-- Source admissibility and nonnegativity identify the actual extended integral,
including its a.e. finite guard; infinity is never totalized before this step. -/
theorem FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential (φ : E → EReal) (hφ : PotentialIntegrable φ μ)
    (hnn : ∀ x, 0 ≤ φ x) :
    AEMeasurable (fun x => (φ x).toENNReal) μ ∧
      (∫⁻ x, (φ x).toENNReal ∂μ) = ENNReal.ofReal (∫ x, (φ x).toReal ∂μ) ∧
      0 ≤ ∫ x, (φ x).toReal ∂μ := by
  have heq : (fun x => (φ x).toENNReal) =ᵐ[μ] (fun x => ENNReal.ofReal (φ x).toReal) := by
    filter_upwards [hφ.2.1] with x hx
    exact EReal.toENNReal_of_ne_top hx
  have hm := hφ.2.2.aemeasurable.ennreal_ofReal
  refine ⟨hm.congr heq.symm, ?_, integral_nonneg (fun x => EReal.toReal_nonneg (hnn x))⟩
  rw [lintegral_congr_ae heq]
  exact (ofReal_integral_eq_lintegral_ofReal hφ.2.2
    (Eventually.of_forall fun x => EReal.toReal_nonneg (hnn x))).symm
end Integral
end
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
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.CEK
end FunctionalInequalities.KLS.CEK
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.CEK
open FunctionalInequalities.Analysis
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.KLS.CEK
end FunctionalInequalities.KLS.CEK
open FunctionalInequalities.KLS.CEK in
/-- A fixed finite real upper bound over ALL source admissible competitors.
The upper bound is derived by actual epsilon reduction; neither convexity of
f nor finite/positive conjugate mass nor finite functional value is assumed. -/
theorem solution (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hfirst : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ U : ℝ, ∀ f : E → EReal, FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f μ →
      FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ f ≤ (U : EReal) := by
  obtain ⟨A, _hA, hc⟩ := FunctionalInequalities.Probability.MomentMeasure.exists_coercivity_of_centered_probability_408915f dx μ hsub hfirst hbar
  let U : ℝ := Real.log A + (Module.finrank ℝ E : ℝ) * Real.log (2 * ((Module.finrank ℝ E : ℝ) + 1))
  refine ⟨U, ?_⟩
  intro f hf
  have heps : ∀ ε : ℝ, 0 < ε → FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ f ≤ ((U + ε : ℝ) : EReal) := by
    intro ε hε
    obtain ⟨ψ, hconv, hp, hnn, hzero, hvalue⟩ := FunctionalInequalities.KLS.CEK.exists_normalized_competitor_408915f dx μ hsub hfirst hbar f hf ε hε
    have hnorm := (hc ψ hnn hzero hconv hp).2
    have hM := (FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential ψ hp hnn).2.2
    have hreal := FunctionalInequalities.Probability.MomentMeasure.real_coercivity_le_uniform_408915f A (Module.finrank ℝ E) (∫ x, (ψ x).toReal ∂μ) hM
    have hψ : FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ ψ ≤ (U : EReal) :=
      hnorm.trans (EReal.coe_le_coe_iff.mpr hreal)
    simpa only [EReal.coe_add] using hvalue.trans (add_le_add hψ (le_refl (ε : EReal)))
  have ht : Tendsto (fun ε : ℝ => ((U + ε : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (U : EReal)) := by
    have hc : Continuous (fun ε : ℝ => ((U + ε : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp (continuous_const.add continuous_id)
    simpa only [add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact heps ε hε
