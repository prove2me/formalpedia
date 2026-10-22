-- Prove2me | solution 1 for FullFormalization.liftedHuberWith_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:58:15.664279+00:00
-- url     : https://prove2.me/submissions/64de2e57-a242-4586-8b8d-91262fbdf978

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
import Theorems.Thm_FullFormalization_Hc_eq_zero
import Theorems.Thm_FullFormalization_Hc_nonneg
import Theorems.Thm_FullFormalization_Hc_of_abs_le
import Theorems.Thm_FullFormalization_Hc_of_le_abs

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

theorem solution {c : ℝ} (hc : 0 < c) {u : E} {z : E}
    (h : liftedHuberWith c u z = 0) : z = u := by
  rw [liftedHuberWith] at h
  have hc0 : 0 ≤ c := le_of_lt hc
  have hnn := Hc_nonneg hc0 (⟪u, z⟫ - 1)
  have hsq : (0 : ℝ) ≤ ‖z - ⟪u, z⟫ • u‖ ^ 2 := sq_nonneg _
  have h1 : Hc c (⟪u, z⟫ - 1) = 0 := by linarith
  have h2 : ⟪u, z⟫ - 1 = 0 := Hc_eq_zero hc h1
  have h3 : ‖z - ⟪u, z⟫ • u‖ ^ 2 = 0 := by linarith
  have h4 : z - ⟪u, z⟫ • u = 0 := by
    have h5 : ‖z - ⟪u, z⟫ • u‖ = 0 := by
      have h5' : ‖z - ⟪u, z⟫ • u‖ * ‖z - ⟪u, z⟫ • u‖ = 0 := by
        rw [← pow_two]
        exact h3
      exact mul_self_eq_zero.mp h5'
    exact norm_eq_zero.mp h5
  have h6 : z = ⟪u, z⟫ • u := sub_eq_zero.mp h4
  have h7 : ⟪u, z⟫ = 1 := by linarith
  rw [h6, h7, one_smul]
