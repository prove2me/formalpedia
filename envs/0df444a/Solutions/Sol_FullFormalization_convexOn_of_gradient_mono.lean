-- Prove2me | solution 1 for FullFormalization.convexOn_of_gradient_mono
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:37:42.845984+00:00
-- url     : https://prove2.me/submissions/b0cd974a-de15-48b6-ae4e-a6a0222230b2

-- Generated from F:/20261008/FullFormalization\FullFormalization\LiftedHuber.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.LiftedHuber

  Source sections 25-26: the *common extremal function* of Theorem B.

  Fix `d j = j (j+7) / 8` (4.1) and a unit vector `u`.  With

      c = 1 / (2 d_N + 1)                                           (25.1)
      H_c(t) = t^2/2  for |t| ≤ c,   c |t| - c^2/2  for |t| ≥ c     (25.2)

  the source defines

      f_N(z) = H_c(⟪u,z⟫ - 1) + (1/2) ‖z - ⟪u,z⟫ u‖²                (25.3)

  Section 26 then records:

  * (26.1) the orthogonal decomposition `z = t u + w`, `w ⊥ u`, along which
    `f_N(z) = H_c(t - 1) + (1/2)‖w‖²`;
  * (26.2) the unique minimiser `z* = u`, `f_N* = 0`, `‖z*‖ = 1`;
  * (26.3) the gradient `∇f_N(z) = clip(⟪u,z⟫-1, -c, c) u + (z - ⟪u,z⟫ u)`,
    whose two summands live in the orthogonal subspaces `span u` and `u^⊥` and
    are each 1-Lipschitz, whence `f_N` is convex, differentiable and globally
    1-smooth;
  * (26.4)-(26.6) the linear-branch formulas on `t ≤ 1 - c`.

  Everything below is proved, nothing is postulated.  The single genuinely
  analytic point is `hasDerivAt_Hc`: the Huber function is differentiable
  everywhere, including at the two kinks `t = ±c`, where the quadratic and
  linear branches paste together smoothly.  Those two points are handled by
  gluing the one-sided derivatives with `HasDerivWithinAt.union`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_LiftedHuber

open scoped Gradient RealInnerProductSpace Topology
open Set
open InnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### The clipping map of (26.3) -/

















/-! ### The Huber function (25.2) -/













/-! ### Differentiability of the Huber function

The only non-elementary point is `|t| = c`, where the branch is a smooth paste
of `t²/2` and `c|t| - c²/2`: on `Iic c` the function agrees with `t²/2` near
`c`, on `Ici c` it agrees with `c t - c²/2`, and both one-sided derivatives at
`c` equal `c`.  The two one-sided statements are glued with
`HasDerivWithinAt.union`. -/







/-! ### Orthogonal decomposition in the direction `u` -/

















/-! ### The gradient of `H_c(⟪u,·⟫ - 1)` -/



/-! ### The gradient of `(1/2)‖z - ⟪u,z⟫ u‖²` -/



/-! ### The lifted Huber function (25.3) -/











/-! ### The gradient (26.3) -/







/-! ### Convexity, via monotonicity of the gradient -/







/-! ### The gradient is globally 1-Lipschitz

The first summand of (26.3) lies in `span u`, the second in `u^⊥`; the two
components of `a - b` decompose the same way, so Pythagoras reduces the claim to
the 1-Lipschitzness of the clipping. -/



/-! ### The minimum of the lifted Huber function (26.2) -/







/-! ### The linear branch (26.4)-(26.6) -/





/-! ### The source's cutoff, and the specialization to `liftedHuber` -/





























end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace Topology
open Set
open InnerProductSpace
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open FullFormalization in

theorem solution {f : E → ℝ} (hd : Differentiable ℝ f)
    (hmono : ∀ a b : E, 0 ≤ ⟪∇ f a - ∇ f b, a - b⟫) : ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  set A : ℝ → E := fun t => x + t • (y - x) with hA
  have hApt : ∀ t : ℝ, A t = x + t • (y - x) := fun t => by rw [hA]
  have hA0 : A 0 = x := by rw [hApt]; simp
  have hA1 : A 1 = y := by rw [hApt]; simp
  have hAderiv : ∀ t : ℝ, HasDerivAt A (y - x) t := by
    intro t
    have h : HasDerivAt (fun s : ℝ => x + s • (y - x)) ((0 : E) + (1 : ℝ) • (y - x)) t :=
      (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const (y - x))
    rw [hA]
    simpa using h
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f (A s)) (fderiv ℝ f (A t) (y - x)) t := by
    intro t
    exact (hd (A t)).hasFDerivAt.comp_hasDerivAt t (hAderiv t)
  have hmono' : MonotoneOn (deriv fun s : ℝ => f (A s)) (interior (Set.Icc (0 : ℝ) 1)) := by
    intro s hs t ht hst
    rw [interior_Icc] at hs ht
    rw [(hderiv s).deriv, (hderiv t).deriv]
    rcases lt_or_eq_of_le hst with hlt | heq
    · have hkey : 0 ≤ ⟪∇ f (A t) - ∇ f (A s), A t - A s⟫ := hmono (A t) (A s)
      have hAs : A t - A s = (t - s) • (y - x) := by
        rw [hApt, hApt]
        module
      rw [hAs, real_inner_smul_right] at hkey
      rw [inner_sub_left, inner_gradient_left, inner_gradient_left] at hkey
      have hpos : 0 < t - s := by linarith
      have h2 : 0 ≤ fderiv ℝ f (A t) (y - x) - fderiv ℝ f (A s) (y - x) :=
        nonneg_of_mul_nonneg_right hkey hpos
      linarith
    · rw [heq]
  have hcont : ContinuousOn (fun s : ℝ => f (A s)) (Set.Icc (0 : ℝ) 1) := by
    have hAc : Continuous A := by
      rw [hA]
      fun_prop
    exact (hd.continuous.comp hAc).continuousOn
  have hdiff : DifferentiableOn ℝ (fun s : ℝ => f (A s)) (interior (Set.Icc (0 : ℝ) 1)) :=
    fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
  have hconv := hmono'.convexOn_of_deriv (convex_Icc (0 : ℝ) 1) hcont hdiff
  obtain ⟨-, hconvI⟩ := hconv
  have hmem0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hmem1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have happ := hconvI hmem0 hmem1 ha hb hab
  have hb0 : a • (0 : ℝ) + b • 1 = b := by simp
  rw [hb0] at happ
  simp only [] at happ
  rw [hA0, hA1] at happ
  have hab' : a = 1 - b := by linarith
  have hAb : A b = a • x + b • y := by
    rw [hApt b, hab']
    module
  rw [hAb] at happ
  exact happ
