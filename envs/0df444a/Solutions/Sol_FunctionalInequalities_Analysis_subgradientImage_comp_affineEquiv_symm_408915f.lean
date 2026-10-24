-- Prove2me | solution 1 for FunctionalInequalities.Analysis.subgradientImage_comp_affineEquiv_symm_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:09:16.720785+00:00
-- url     : https://prove2.me/submissions/a1ebead7-cd72-4058-b67a-21e257fbe6f2

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
section LT11E1AffineTransportSubgradientimage
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section StructuredSpace
variable {E : Type*}
variable [NormedAddCommGroup E]
private lemma FunctionalInequalities.Analysis.affineEquiv_linear_sub
    [Module ℝ E] (e : E ≃ᵃ[ℝ] E) (a b : E) :
    (e.linear : E →ₗ[ℝ] E) (a - b) = e a - e b := by
  change (AffineEquiv.toAffineMap e).linear (a - b) =
    (AffineEquiv.toAffineMap e) a - (AffineEquiv.toAffineMap e) b
  exact (AffineEquiv.toAffineMap e).linearMap_vsub a b
section FiniteDimensional
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- **Affine transport of subgradient images** (weak Letwin route, Caffarelli's argument):
under an affine equivalence `e` with linear part `T`, the subgradient image of `u ∘ e.symm` over
`e '' G` is the image of `∂u(G)` under the adjoint of `T⁻¹`. -/
theorem solution (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    FunctionalInequalities.Analysis.subgradientImage (u ∘ e.symm) (e '' G) =
      (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) '' FunctionalInequalities.Analysis.subgradientImage u G := by
  ext q
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, hq⟩
    let p : E := LinearMap.adjoint (e.linear : E →ₗ[ℝ] E) q
    have hcomp :
        (e.linear : E →ₗ[ℝ] E) ∘ₗ (e.linear.symm : E →ₗ[ℝ] E) =
          LinearMap.id := by
      ext v
      simp
    have hadjcomp :
        LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) ∘ₗ
            LinearMap.adjoint (e.linear : E →ₗ[ℝ] E) =
          LinearMap.id := by
      calc
        LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) ∘ₗ
              LinearMap.adjoint (e.linear : E →ₗ[ℝ] E) =
            LinearMap.adjoint
              ((e.linear : E →ₗ[ℝ] E) ∘ₗ (e.linear.symm : E →ₗ[ℝ] E)) :=
          (LinearMap.adjoint_comp (e.linear : E →ₗ[ℝ] E)
            (e.linear.symm : E →ₗ[ℝ] E)).symm
        _ = LinearMap.adjoint LinearMap.id := by rw [hcomp]
        _ = LinearMap.id := LinearMap.adjoint_id
    have hadj :
        LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) p = q := by
      have h := congrArg (fun f : E →ₗ[ℝ] E => f q) hadjcomp
      simpa [p] using h
    have hp : p ∈ FunctionalInequalities.Analysis.subgradientImage u G := by
      refine ⟨x, hx, ?_⟩
      intro y
      have hi :
          inner ℝ q (e y - e x) = inner ℝ p (y - x) := by
        calc
          inner ℝ q (e y - e x) =
              inner ℝ ((e.linear : E →ₗ[ℝ] E) (y - x)) q := by
            rw [affineEquiv_linear_sub e y x]
            exact (real_inner_comm q (e y - e x)).symm
          _ = inner ℝ (y - x) p := by
            simpa [p] using
              (LinearMap.adjoint_inner_right (e.linear : E →ₗ[ℝ] E) (y - x) q).symm
          _ = inner ℝ p (y - x) := real_inner_comm p (y - x)
      calc
        u x + inner ℝ p (y - x) =
            u x + inner ℝ q (e y - e x) := by rw [hi]
        _ ≤ u y := by
          simpa only [Function.comp_apply, e.symm_apply_apply] using hq (e y)
    refine ⟨p, hp, ?_⟩
    exact hadj
  · rintro ⟨p, hp, hpq⟩
    rcases hp with ⟨x, hx, hpx⟩
    refine ⟨e x, ⟨x, hx, rfl⟩, ?_⟩
    rw [← hpq]
    intro z
    have hlin :
        (e.symm.linear : E →ₗ[ℝ] E) =
          (e.linear.symm : E →ₗ[ℝ] E) := by
      ext v
      simp
    have hv :
        (e.linear.symm : E →ₗ[ℝ] E) (z - e x) = e.symm z - x := by
      calc
        (e.linear.symm : E →ₗ[ℝ] E) (z - e x) =
            (e.symm.linear : E →ₗ[ℝ] E) (z - e x) := by
              rw [hlin]
        _ = e.symm z - e.symm (e x) :=
          affineEquiv_linear_sub e.symm z (e x)
        _ = e.symm z - x := by rw [e.symm_apply_apply]
    have hi :
        inner ℝ (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) p) (z - e x) =
          inner ℝ p (e.symm z - x) := by
      calc
        inner ℝ (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) p) (z - e x) =
            inner ℝ (z - e x)
              (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E) p) := by
          rw [real_inner_comm]
        _ = inner ℝ ((e.linear.symm : E →ₗ[ℝ] E) (z - e x)) p :=
          LinearMap.adjoint_inner_right (e.linear.symm : E →ₗ[ℝ] E) (z - e x) p
        _ = inner ℝ (e.symm z - x) p := by rw [hv]
        _ = inner ℝ p (e.symm z - x) :=
          real_inner_comm p (e.symm z - x)
    simpa only [Function.comp_apply, e.symm_apply_apply, hi] using hpx (e.symm z)
