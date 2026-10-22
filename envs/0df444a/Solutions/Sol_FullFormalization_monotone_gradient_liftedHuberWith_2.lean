-- Prove2me | solution 2 for FullFormalization.monotone_gradient_liftedHuberWith
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T07:56:09.377992+00:00
-- url     : https://prove2.me/submissions/80a0fa3b-b1fd-4dd4-bfe2-1d031a806d83

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
import Theorems.Thm_FullFormalization_Hc_of_abs_le
import Theorems.Thm_FullFormalization_Hc_of_le_abs
import Theorems.Thm_FullFormalization_clip_eq_max
import Theorems.Thm_FullFormalization_clip_le_left
import Theorems.Thm_FullFormalization_clip_neg
import Theorems.Thm_FullFormalization_clip_pos
import Theorems.Thm_FullFormalization_clip_self
import Theorems.Thm_FullFormalization_gradient_liftedHuberWith
import Theorems.Thm_FullFormalization_hasDerivAt_Hc
import Theorems.Thm_FullFormalization_hasFDerivAt_Hc_inner
import Theorems.Thm_FullFormalization_hasFDerivAt_half_norm_sq
import Theorems.Thm_FullFormalization_hasFDerivAt_liftedHuberWith
import Theorems.Thm_FullFormalization_hasFDerivAt_orthProj
import Theorems.Thm_FullFormalization_inner_orthProj
import Theorems.Thm_FullFormalization_inner_orthProj_left
import Theorems.Thm_FullFormalization_inner_u_self
import Theorems.Thm_FullFormalization_monotone_clip
import Theorems.Thm_FullFormalization_orthProjL_apply

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
theorem solution (c : ℝ) (hc : 0 < c) (u : E) (hu : ‖u‖ = 1) :
    ∀ a b : E, 0 ≤ ⟪∇ (liftedHuberWith c u) a - ∇ (liftedHuberWith c u) b, a - b⟫ := by
  intro a b
  rw [gradient_liftedHuberWith c hc u a hu, gradient_liftedHuberWith c hc u b hu]
  set Aa : ℝ := clip (⟪u, a⟫ - 1) (-c) c with hAa
  set Ab : ℝ := clip (⟪u, b⟫ - 1) (-c) c with hAb
  set wa : E := a - ⟪u, a⟫ • u with hwa
  set wb : E := b - ⟪u, b⟫ • u with hwb
  have hwag : ⟪u, wa⟫ = 0 := by
    rw [hwa]
    simpa only [orthProj] using inner_orthProj hu a
  have hwbg : ⟪u, wb⟫ = 0 := by
    rw [hwb]
    simpa only [orthProj] using inner_orthProj hu b
  have hperp : ⟪u, wa - wb⟫ = 0 := by rw [inner_sub_right, hwag, hwbg, sub_zero]
  have hperpL : ⟪wa - wb, u⟫ = 0 := by rw [real_inner_comm]; exact hperp
  have hgrad : Aa • u + wa - (Ab • u + wb) = (Aa - Ab) • u + (wa - wb) := by module
  have hsub2 : (⟪u, a⟫ • u + wa) - (⟪u, b⟫ • u + wb)
      = (⟪u, a⟫ - ⟪u, b⟫) • u + (wa - wb) := by module
  have hsub1 : a - b = (⟪u, a⟫ • u + wa) - (⟪u, b⟫ • u + wb) := by
    have ha : a = ⟪u, a⟫ • u + wa := by rw [hwa]; abel
    have hb : b = ⟪u, b⟫ • u + wb := by rw [hwb]; abel
    rw [← ha, ← hb]
  have hsub : a - b = (⟪u, a⟫ - ⟪u, b⟫) • u + (wa - wb) := hsub1.trans hsub2
  rw [hgrad, hsub]
  have hsign : 0 ≤ (Aa - Ab) * (⟪u, a⟫ - ⟪u, b⟫) := by
    rcases le_total ⟪u, a⟫ ⟪u, b⟫ with h | h
    · have h1 : Aa ≤ Ab := by
        rw [hAa, hAb]
        exact monotone_clip (-c) c (by linarith)
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have h1 : Ab ≤ Aa := by
        rw [hAb, hAa]
        exact monotone_clip (-c) c (by linarith)
      exact mul_nonneg (by linarith) (by linarith)
  have hexp : ⟪(Aa - Ab) • u + (wa - wb), (⟪u, a⟫ - ⟪u, b⟫) • u + (wa - wb)⟫
      = (Aa - Ab) * (⟪u, a⟫ - ⟪u, b⟫) + ⟪wa - wb, wa - wb⟫ := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hperp, hperpL, inner_u_self hu, mul_zero, zero_add, add_zero, mul_one]
    ring
  rw [hexp]
  have hnn : 0 ≤ ⟪wa - wb, wa - wb⟫ := by
    rw [real_inner_self_eq_norm_sq]
    positivity
  linarith
