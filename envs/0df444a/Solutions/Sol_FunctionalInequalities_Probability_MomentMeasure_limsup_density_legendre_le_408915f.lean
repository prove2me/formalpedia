-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.limsup_density_legendre_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:28:52.725737+00:00
-- url     : https://prove2.me/submissions/e086fe0b-c401-4a30-9252-ec0888d3f7e0

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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
/-- Pointwise conjugate-density limsup control from actual interior convergence.
No convergence of the conjugates is assumed. Infinite conjugates and density zero
are retained through the EReal exponential order isomorphism. -/
theorem solution
    (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
    (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
    (hsup : ∀ y, FunctionalInequalities.Analysis.legendre ψ y = ⨆ x ∈ K, (inner ℝ x y : EReal) - ψ x)
    (y : E) :
    limsup (fun j => FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre (φ j)) y) atTop ≤ FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre ψ) y := by
  let L := limsup (fun j => FunctionalInequalities.Probability.MomentMeasure.density (FunctionalInequalities.Analysis.legendre (φ j)) y) atTop
  have hbound : FunctionalInequalities.Analysis.legendre ψ y ≤ -ENNReal.log L := by
    rw [hsup y]
    apply iSup_le
    intro x
    apply iSup_le
    intro hx
    have hneg : Tendsto (fun j => -( (inner ℝ x y : EReal) - φ j x)) atTop
        (𝓝 (-((inner ℝ x y : EReal) - ψ x))) := by
      have hc := (EReal.continuousAt_add (p := (-(inner ℝ x y : EReal), ψ x))
        (.inl (by simp)) (.inl (by simp))).tendsto.comp
          (tendsto_const_nhds.prodMk_nhds (hlim x hx))
      simpa only [EReal.neg_sub (.inl (EReal.coe_ne_bot _))
        (.inl (EReal.coe_ne_top _)), Function.comp_def] using hc
    have hexp := (EReal.expOrderIso.continuous.tendsto _).comp hneg
    have hL : L ≤ EReal.exp (-((inner ℝ x y : EReal) - ψ x)) := by
      calc
        L ≤ limsup (fun j => EReal.exp (-((inner ℝ x y : EReal) - φ j x))) atTop :=
          limsup_le_limsup (Eventually.of_forall fun j =>
            EReal.exp_monotone (EReal.neg_le_neg_iff.mpr
              (le_iSup (fun z : E => (inner ℝ z y : EReal) - φ j z) x)))
        _ = _ := hexp.limsup_eq
    have hlog : ENNReal.log L ≤ -((inner ℝ x y : EReal) - ψ x) := by
      simpa only [ENNReal.logOrderIso_apply, EReal.log_exp] using ENNReal.logOrderIso.monotone hL
    simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr hlog
  have hn : ENNReal.log L ≤ -FunctionalInequalities.Analysis.legendre ψ y := by
    simpa only [neg_neg] using EReal.neg_le_neg_iff.mpr hbound
  simpa only [ENNReal.exp_log, L, FunctionalInequalities.Probability.MomentMeasure.density] using EReal.exp_monotone hn
