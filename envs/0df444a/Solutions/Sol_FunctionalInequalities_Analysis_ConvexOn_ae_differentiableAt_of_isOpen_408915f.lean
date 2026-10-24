-- Prove2me | solution 1 for FunctionalInequalities.Analysis.ConvexOn.ae_differentiableAt_of_isOpen_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:51:37.476301+00:00
-- url     : https://prove2.me/submissions/5e8436cd-e969-407e-b3cd-b73142b2460b

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section LT14A0ConvexAeDifferentiable
open MeasureTheory Set
namespace FunctionalInequalities.Analysis.ConvexOn
end FunctionalInequalities.Analysis.ConvexOn
open FunctionalInequalities.Analysis.ConvexOn in
/-- **A convex function on an open set is differentiable almost everywhere on it** (Rademacher for
convex functions; weak Letwin route, support for the a.e. injectivity of the subgradient map). -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {U : Set E} (hU : IsOpen U) {f : E → ℝ} (hf : ConvexOn ℝ U f) :
    ∀ᵐ x ∂μ, x ∈ U → DifferentiableAt ℝ f x := by
  let I := {x : E // x ∈ U}
  have hball : ∀ x : I, ∃ q : ℝ × NNReal,
      0 < q.1 ∧ LipschitzOnWith q.2 f (Metric.ball (x : E) q.1) ∧
        Metric.ball (x : E) q.1 ⊆ U := by
    intro x
    rcases hf.locallyLipschitzOn hU x.property with ⟨K, t, ht, hK⟩
    have hU_nhds : U ∈ nhds (x : E) := hU.mem_nhds x.property
    have hnhds : nhdsWithin (x : E) U = nhds (x : E) :=
      nhdsWithin_eq_nhds.mpr hU_nhds
    have htx : t ∈ nhds (x : E) := by
      rw [← hnhds]
      exact ht
    rcases Metric.mem_nhds_iff.mp
        (Filter.inter_mem htx (hU.mem_nhds x.property)) with ⟨r, hr, hrt⟩
    exact ⟨(r, K), hr, hK.mono (hrt.trans inter_subset_left),
      hrt.trans inter_subset_right⟩
  let q : I → ℝ × NNReal := fun x => Classical.choose (hball x)
  let B : I → Set E := fun x => Metric.ball (x : E) (q x).1
  have hq : ∀ x : I, 0 < (q x).1 ∧ LipschitzOnWith (q x).2 f (B x) ∧ B x ⊆ U := by
    intro x
    exact Classical.choose_spec (hball x)
  have hAE : ∀ x : I, ∀ᵐ y ∂μ, y ∈ B x → DifferentiableAt ℝ f y := by
    intro x
    filter_upwards [(hq x).2.1.ae_differentiableWithinAt_of_mem] with y hy
    intro hyB
    exact (hy hyB).differentiableAt (Metric.isOpen_ball.mem_nhds hyB)
  obtain ⟨T, hT, hTU⟩ :=
    TopologicalSpace.isOpen_iUnion_countable B (fun x => Metric.isOpen_ball)
  have hTcount : Countable T := hT.to_subtype
  have hBU : (⋃ x, B x) = U := by
    apply Subset.antisymm
    · exact iUnion_subset fun x => (hq x).2.2
    · intro y hy
      let x : I := ⟨y, hy⟩
      exact mem_iUnion.2 ⟨x, Metric.mem_ball_self (hq x).1⟩
  have hAEall : ∀ᵐ y ∂μ, ∀ x : T, y ∈ B (x : I) →
      DifferentiableAt ℝ f y := by
    exact ae_all_iff.2 (fun x => hAE (x : I))
  filter_upwards [hAEall] with y hy
  intro hyU
  have hyT : y ∈ ⋃ x ∈ T, B x := by
    rw [hTU, hBU]
    exact hyU
  rcases mem_iUnion₂.mp hyT with ⟨x, hxT, hyx⟩
  exact hy ⟨x, hxT⟩ hyx
