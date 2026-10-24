-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.exists_integral_bound_of_eventual_functional_lower_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:41:00.567762+00:00
-- url     : https://prove2.me/submissions/02e82ded-6d56-4f61-9427-cf281003c111

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
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_bound_of_log_lower_408915f
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_exists_coercivity_of_centered_probability_408915f

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
section FiniteDimensional
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
variable [BorelSpace E]
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
/-- Actual normalized-sequence integral control from a finite eventual
functional lower bound, as in CEK (62). The finite prefix is handled by the
proved bounded-range theorem; no desired sequence bound is supplied. -/
theorem solution
    (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0)
    (φ : ℕ → E → EReal) (hnn : ∀ j x, 0 ≤ φ j x) (hφ0 : ∀ j, φ j 0 = 0)
    (hconv : ∀ j, FunctionalInequalities.Analysis.ConvexPotential (φ j)) (hφ : ∀ j, FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable (φ j) μ)
    (b : ℝ) (hlower : ∀ᶠ j in atTop, (b : EReal) ≤ FunctionalInequalities.Probability.MomentMeasure.variationalFunctional dx μ (φ j)) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ j, (∫ x, (φ j x).toReal ∂μ) ≤ B) ∧
      (⨆ j, ∫⁻ x, (φ j x).toENNReal ∂μ) ≠ ⊤ := by
  obtain ⟨A, _hA, hc⟩ := FunctionalInequalities.Probability.MomentMeasure.exists_coercivity_of_centered_probability_408915f dx μ hsub hint hbar
  obtain ⟨B, _hB, hlogbound⟩ := FunctionalInequalities.Probability.MomentMeasure.exists_bound_of_log_lower_408915f A (Module.finrank ℝ E) b
  have hev : ∀ᶠ j in atTop, (∫ x, (φ j x).toReal ∂μ) ≤ B := by
    filter_upwards [hlower] with j hj
    apply hlogbound _ (FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential (φ j) (hφ j) (hnn j)).2.2
    exact EReal.coe_le_coe_iff.mp (hj.trans (hc (φ j) (hnn j) (hφ0 j) (hconv j) (hφ j)).2)
  have hbu : IsBoundedUnder (fun a b : ℝ => a ≤ b) atTop (fun j => ∫ x, (φ j x).toReal ∂μ) := ⟨B, hev⟩
  obtain ⟨B', hB'⟩ := hbu.bddAbove_range
  refine ⟨max B' 0, le_max_right _ _, ?_, ?_⟩
  · intro j
    exact (hB' (mem_range_self j)).trans (le_max_left _ _)
  · apply ne_top_of_le_ne_top (b := ENNReal.ofReal (max B' 0)) ENNReal.ofReal_ne_top
    apply iSup_le
    intro j
    rw [(FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential (φ j) (hφ j) (hnn j)).2.1]
    exact ENNReal.ofReal_le_ofReal ((hB' (mem_range_self j)).trans (le_max_left _ _))
