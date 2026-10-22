-- Prove2me | solution 1 for FullFormalization.Ival_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:55:56.746199+00:00
-- url     : https://prove2.me/submissions/f2d8c224-1b95-4041-b172-07986d92b8ed

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
import Theorems.Thm_FullFormalization_convexOn_le_gradient
import Theorems.Thm_FullFormalization_descent_lemma
import Theorems.Thm_FullFormalization_differentiable_inner_const
import Theorems.Thm_FullFormalization_gradient_inner_const
import Theorems.Thm_FullFormalization_gradient_sub
import Theorems.Thm_FullFormalization_gradient_sub_inner

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
    (hd : Differentiable ℝ f) (hsm : ∀ a b : E, ‖∇ f a - ∇ f b‖ ≤ ‖a - b‖) (x y : E) :
    0 ≤ Ival (f x) (f y) x y (∇ f x) (∇ f y) := by
  set φ : E → ℝ := fun z => f z - ⟪∇ f y, z⟫ with hφ
  have hφdiff : Differentiable ℝ φ := hd.sub (differentiable_inner_const (∇ f y))
  have hφgrad : ∀ z : E, ∇ φ z = ∇ f z - ∇ f y := by
    intro z
    simpa [hφ] using gradient_sub_inner f (∇ f y) z (hd z)
  have hφsm : ∀ a b : E, ‖∇ φ a - ∇ φ b‖ ≤ ‖a - b‖ := by
    intro a b
    rw [hφgrad a, hφgrad b]
    have hsub : ∇ f a - ∇ f y - (∇ f b - ∇ f y) = ∇ f a - ∇ f b := by abel
    rw [hsub]
    exact hsm a b
  have hdesc : φ (x - (∇ f x - ∇ f y)) ≤ φ x - (1 / 2) * ‖∇ f x - ∇ f y‖ ^ 2 := by
    have h := descent_lemma hφdiff hφsm x
    rwa [hφgrad x] at h
  have hconv_le := convexOn_le_gradient hconv hd y (x - (∇ f x - ∇ f y))
  have hstep : φ y ≤ φ (x - (∇ f x - ∇ f y)) := by
    simp only [hφ]
    have h := hconv_le
    rw [inner_sub_right] at h
    linarith
  have hchain : φ y ≤ φ x - (1 / 2) * ‖∇ f x - ∇ f y‖ ^ 2 := le_trans hstep hdesc
  simp only [hφ] at hchain
  simp only [Ival]
  rw [inner_sub_right]
  linarith
