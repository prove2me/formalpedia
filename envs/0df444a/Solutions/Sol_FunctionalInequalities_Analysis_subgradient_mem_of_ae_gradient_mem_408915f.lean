-- Prove2me | solution 1 for FunctionalInequalities.Analysis.subgradient_mem_of_ae_gradient_mem_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:11:41.910309+00:00
-- url     : https://prove2.me/submissions/b26384dc-6d58-4ce9-8e11-1f4c5fb3981b

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
section SubgradientRange
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
private lemma FunctionalInequalities.Analysis.gradient_le_increment [CompleteSpace E]
    {u : E → ℝ} (hc : ConvexOn ℝ univ u)
    (z v : E) (hz : DifferentiableAt ℝ u z) :
    ⟪gradient u z, v⟫ ≤ u (z + v) - u z := by
  have hd :
      HasFDerivAt u ((InnerProductSpace.toDual ℝ E) (gradient u z))
        ((AffineMap.lineMap (k := ℝ) z (z + v)) (0 : ℝ)) := by
    simpa only [AffineMap.lineMap_apply_zero] using hz.hasGradientAt.hasFDerivAt
  have hl :
      HasDerivAt (u ∘ ⇑(AffineMap.lineMap (k := ℝ) z (z + v)))
        ⟪gradient u z, v⟫ (0 : ℝ) := by
    simpa only [add_sub_cancel_left, InnerProductSpace.toDual_apply_apply] using
      hd.comp_hasDerivAt 0
        (AffineMap.hasDerivAt_lineMap (a := z) (b := z + v) (x := (0 : ℝ)))
  have hcl :
      ConvexOn ℝ univ (u ∘ ⇑(AffineMap.lineMap (k := ℝ) z (z + v))) := by
    simpa only [preimage_univ] using
      ConvexOn.comp_affineMap (AffineMap.lineMap (k := ℝ) z (z + v)) hc
  simpa only [slope_def_field, Function.comp_apply,
    AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero, sub_zero, div_one] using
    hcl.le_slope_of_hasDerivAt (mem_univ 0) (mem_univ 1)
      (zero_lt_one : (0 : ℝ) < 1) hl
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Subgradients of a convex Lipschitz function lie in the closed convex range of its a.e.
gradient** (weak Letwin route: `∂u(x) ⊆ K̄` for the weak moment map, whose gradient lies
a.e. in the target `K`): if `u` is convex and Lipschitz on a finite-dimensional inner product space,
`K` is closed and convex and `∇u(x) ∈ K` for a.e. `x`, then every subgradient `p` of `u` at every
point `x` (`u(x) + ⟪p, y − x⟫ ≤ u(y)` for all `y`) lies in `K`. -/
theorem solution [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u : E → ℝ} {L : NNReal} (hu : LipschitzWith L u) (hconv : ConvexOn ℝ univ u)
    {K : Set E} (hK : IsClosed K) (hKc : Convex ℝ K)
    (hae : ∀ᵐ x ∂(volume : Measure E), gradient u x ∈ K)
    {x p : E} (hp : ∀ y, u x + ⟪p, y - x⟫ ≤ u y) : p ∈ K := by
  by_contra hpn
  obtain ⟨f, s, hps, hsep⟩ :=
    geometric_hahn_banach_point_closed hKc hK hpn
  let θ : E := (InnerProductSpace.toDual ℝ E).symm f
  have hθ : ∀ q : E, ⟪q, θ⟫ = f q := by
    intro q
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply

  -- The differentiability points with gradient in K form a dense set.
  have hdense : Dense {z | DifferentiableAt ℝ u z ∧ gradient u z ∈ K} :=
    MeasureTheory.Measure.dense_of_ae
      ((hu.ae_differentiableAt (μ := (volume : Measure E))).and hae)

  -- Convexity gives the bound on the dense set; continuity extends it everywhere.
  have hbound :
      ∀ z ∈ {z | DifferentiableAt ℝ u z ∧ gradient u z ∈ K},
        s ≤ u (z + θ) - u z := by
    intro z hz
    exact (hsep _ hz.2).le.trans
      ((hθ (gradient u z)) ▸ gradient_le_increment hconv z θ hz.1)
  have hb : ∀ z : E, s ≤ u (z + θ) - u z := by
    intro z
    exact hdense.induction hbound
      (isClosed_le continuous_const
        ((hu.continuous.comp (continuous_id.add_const θ)).sub hu.continuous)) z

  have hb' : s ≤ u x - u (x - θ) := by
    simpa only [sub_add_cancel] using hb (x - θ)
  have hp' := hp (x - θ)
  simp only [sub_sub_cancel_left, inner_neg_right, hθ] at hp'
  linarith
