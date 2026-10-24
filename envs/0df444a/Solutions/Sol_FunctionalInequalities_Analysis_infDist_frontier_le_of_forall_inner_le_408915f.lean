-- Prove2me | solution 1 for FunctionalInequalities.Analysis.infDist_frontier_le_of_forall_inner_le_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:08:17.658327+00:00
-- url     : https://prove2.me/submissions/f0ec5f08-2341-4bcd-b13b-e9a6c5212e94

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
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
open scoped RealInnerProductSpace ENNReal
section LT11E2InfdistLeWidth
open Set Metric
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Distance to the frontier is at most the width in any direction** (weak Letwin route, Caffarelli's argument): for a bounded open `S`, a point `x ∈ S` and a unit vector `θ`, if
`⟪y − x, θ⟫ ≤ t` for all `y ∈ S`, then `infDist x (frontier S) ≤ t`. -/
theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] {S : Set E} (hS : IsOpen S) (hb : Bornology.IsBounded S)
    {x : E} (hx : x ∈ S) {θ : E} (hθ : ‖θ‖ = 1) {t : ℝ} (ht : ∀ y ∈ S, ⟪y - x, θ⟫ ≤ t) :
    infDist x (frontier S) ≤ t := by
  have _ := hb
  have ht0 : 0 ≤ t := by
    simpa using ht x hx
  apply le_of_forall_pos_le_add
  intro η hη
  have ha0 : 0 ≤ t + η := add_nonneg ht0 (le_of_lt hη)
  have hz : x + (t + η) • θ ∉ S := by
    intro hzS
    have hle := ht (x + (t + η) • θ) hzS
    have heq : ⟪(x + (t + η) • θ) - x, θ⟫ = t + η := by
      simp only [add_sub_cancel_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
        hθ, one_pow, mul_one]
    rw [heq] at hle
    linarith
  let f : ℝ → E := fun r => x + r • θ
  let T : Set E := f '' Icc 0 (t + η)
  have hf : Continuous f := by
    dsimp [f]
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hTpc : IsPreconnected T := by
    exact isPreconnected_Icc.image f hf.continuousOn
  have hxT : (T ∩ S).Nonempty := by
    refine ⟨x, ?_, hx⟩
    refine ⟨0, ⟨le_rfl, ha0⟩, ?_⟩
    simp [f]
  have hzT : x + (t + η) • θ ∈ T := by
    refine ⟨t + η, ⟨ha0, le_rfl⟩, ?_⟩
    rfl
  have hfront : (frontier S ∩ T).Nonempty := by
    by_contra hne
    have hclosure : closure S ∩ T ⊆ S := by
      intro y hy
      by_contra hys
      have hyf : y ∈ frontier S := by
        rw [hS.frontier_eq]
        exact ⟨hy.1, hys⟩
      exact hne ⟨y, hyf, hy.2⟩
    have hsub : T ⊆ S :=
      hTpc.subset_of_closure_inter_subset hS hxT hclosure
    exact hz (hsub hzT)
  rcases hfront with ⟨y, hyfront, hyT⟩
  rcases hyT with ⟨r, hr, rfl⟩
  change x + r • θ ∈ frontier S at hyfront
  calc
    infDist x (frontier S) ≤ dist x (x + r • θ) :=
      Metric.infDist_le_dist_of_mem hyfront
    _ = r := by
      rw [dist_self_add_right, norm_smul, Real.norm_eq_abs, hθ, mul_one,
        abs_of_nonneg hr.1]
    _ ≤ t + η := hr.2
