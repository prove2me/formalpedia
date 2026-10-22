-- Prove2me | solution 1 for FullFormalization.convexOn_le_gradient
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:37:14.954991+00:00
-- url     : https://prove2.me/submissions/e0bdaeec-92b3-43f6-ba3f-6902d911908a

-- Generated from F:/20261008/FullFormalization\FullFormalization\SmoothConvex.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.SmoothConvex

  Source section 2: the smooth-convex interpolation residual

      I_{ij} = F_i - F_j - ⟨g_j, x_i - x_j⟩ - (1/2) ‖g_i - g_j‖²  ≥ 0   (2.2)

  and its proof, which the source carries out in full (lines 211-279) rather
  than citing.  Nothing here is an axiom: (2.2) is derived from convexity and
  global 1-Lipschitzness of the gradient, through exactly the two ingredients
  the source uses.

  Source argument (lines 213-277):
    * `φ = f - ⟪g_j, ·⟫` is convex and 1-smooth, and `∇φ(x_j) = 0`, so `x_j`
      minimises `φ`;
    * the descent lemma gives `φ(x_i - ∇φ(x_i)) ≤ φ(x_i) - ½‖∇φ(x_i)‖²`;
    * hence `φ(x_i) - φ(x_j) ≥ ½‖∇φ(x_i)‖²`, which is (2.2).

  The two ingredients are proved here from scratch:

  * `descent_lemma` — for a differentiable `ψ` whose gradient is globally
    1-Lipschitz, `ψ (u - ∇ψ u) ≤ ψ u - ½‖∇ψ u‖²`.  No convexity is used.
    This is the source's `descent lemma` (quoted at line 227).

  * `convexOn_le_gradient` — for convex differentiable `f`,
    `f y ≥ f x + ⟪∇f x, y - x⟫`, which is what makes a zero gradient a global
    minimiser (source line 235: "hence `x_j` is the global minimiser of `φ`").

  Both reduce to one-dimensional calculus along a segment, using Mathlib's
  `ConvexOn.deriv_le_slope` (convexity versus secant slope) and
  `antitoneOn_of_hasDerivWithinAt_nonpos` (a nonpositive derivative makes a
  function antitone), the formal counterpart of integrating the derivative
  bound.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients

open scoped Gradient RealInnerProductSpace
open Set

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Gradient of a difference, and of `⟪c, ·⟫` -/









/-! ### The first-order condition for convex differentiable functions -/



/-! ### The descent lemma for a 1-smooth function (source line 227) -/



/-! ### Lemma 2.1 -/



end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
open Set
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open FullFormalization in

theorem solution {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f)
    (hd : Differentiable ℝ f) (x y : E) :
    f x + ⟪∇ f x, y - x⟫ ≤ f y := by
  set A : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y with hA
  have hpath : ∀ t : ℝ, A t = x + t • (y - x) := by
    intro t
    rw [hA, AffineMap.lineMap_apply]
    simp [vsub_eq_sub, vadd_eq_add, add_comm]
  have hconvG : ConvexOn ℝ Set.univ (fun t : ℝ => f (A t)) := by
    have h := ConvexOn.comp_affineMap A hconv
    rwa [Set.preimage_univ] at h
  have hA0 : A 0 = x := by rw [hpath]; simp
  have hA1 : A 1 = y := by rw [hpath]; simp
  have hAderiv : HasDerivAt (fun t : ℝ => A t) (y - x) 0 := by
    have hfun : (fun t : ℝ => A t) = fun t : ℝ => x + t • (y - x) := funext hpath
    rw [hfun]
    have h : HasDerivAt (fun t : ℝ => x + t • (y - x)) (0 + (1 : ℝ) • (y - x)) 0 :=
      (hasDerivAt_const (0 : ℝ) x).add ((hasDerivAt_id (0 : ℝ)).smul_const (y - x))
    simpa using h
  have hcomp : HasDerivAt (fun t : ℝ => f (A t)) (fderiv ℝ f x (y - x)) 0 := by
    have hdA : HasFDerivAt f (fderiv ℝ f x) (A 0) := by rw [hA0]; exact (hd x).hasFDerivAt
    exact hdA.comp_hasDerivAt (0 : ℝ) hAderiv
  have hderiv : HasDerivAt (fun t : ℝ => f (A t)) (⟪∇ f x, y - x⟫) 0 := by
    have h := hcomp
    rw [← inner_gradient_left] at h
    exact h
  have hslope := hconvG.deriv_le_slope (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num)
    hderiv.differentiableAt
  rw [hderiv.deriv, slope_def_field] at hslope
  simp only [hA1, hA0, sub_zero, div_one] at hslope
  linarith
