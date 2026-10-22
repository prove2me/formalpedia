-- Prove2me | solution 1 for FullFormalization.lipschitz_gradient_liftedHuberWith
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T06:51:33.25284+00:00
-- url     : https://prove2.me/submissions/bc440fe6-bbe2-4244-a60f-e97839f1b7d7

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
import Theorems.Thm_FullFormalization_abs_clip_sub_clip_le
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
    ∀ a b : E, ‖∇ (liftedHuberWith c u) a - ∇ (liftedHuberWith c u) b‖ ≤ ‖a - b‖ := by
  intro a b
  rw [gradient_liftedHuberWith c hc u a hu, gradient_liftedHuberWith c hc u b hu]
  set Aa : ℝ := clip (⟪u, a⟫ - 1) (-c) c with hAa
  set Ab : ℝ := clip (⟪u, b⟫ - 1) (-c) c with hAb
  set wa : E := a - ⟪u, a⟫ • u with hwa
  set wb : E := b - ⟪u, b⟫ • u with hwb
  set W : E := wa - wb with hW
  have hwag : ⟪u, wa⟫ = 0 := by
    rw [hwa]
    simpa only [orthProj] using inner_orthProj hu a
  have hwbg : ⟪u, wb⟫ = 0 := by
    rw [hwb]
    simpa only [orthProj] using inner_orthProj hu b
  have hperp : ⟪u, W⟫ = 0 := by rw [hW, inner_sub_right, hwag, hwbg, sub_zero]
  have hgrad : Aa • u + wa - (Ab • u + wb) = (Aa - Ab) • u + W := by
    rw [hW]
    module
  have hsub2 : (⟪u, a⟫ • u + wa) - (⟪u, b⟫ • u + wb)
      = (⟪u, a⟫ - ⟪u, b⟫) • u + W := by
    rw [hW]
    module
  have hsub1 : a - b = (⟪u, a⟫ • u + wa) - (⟪u, b⟫ • u + wb) := by
    have ha : a = ⟪u, a⟫ • u + wa := by rw [hwa]; abel
    have hb : b = ⟪u, b⟫ • u + wb := by rw [hwb]; abel
    rw [← ha, ← hb]
  have hsub : a - b = (⟪u, a⟫ - ⟪u, b⟫) • u + W := hsub1.trans hsub2
  have habs : |Aa - Ab| ≤ |⟪u, a⟫ - ⟪u, b⟫| := by
    have h := abs_clip_sub_clip_le (⟪u, a⟫ - 1) (⟪u, b⟫ - 1) (-c) c
    have hS' : (⟪u, a⟫ - 1) - (⟪u, b⟫ - 1) = (⟪u, a⟫ - ⟪u, b⟫) := by ring
    rw [hS'] at h
    rwa [← hAa, ← hAb] at h
  have hsq : (Aa - Ab) ^ 2 ≤ (⟪u, a⟫ - ⟪u, b⟫) ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (Aa - Ab)) (abs_nonneg _)).mpr habs
    rwa [sq_abs, sq_abs] at h
  have h2u : ‖u‖ ^ 2 = 1 := by rw [hu]; norm_num
  have hsq1 : ‖(Aa - Ab) • u‖ * ‖(Aa - Ab) • u‖ = (Aa - Ab) ^ 2 := by
    rw [← pow_two, norm_smul, Real.norm_eq_abs, mul_pow, h2u, mul_one, sq_abs]
  have hsq2 : ‖(⟪u, a⟫ - ⟪u, b⟫) • u‖ * ‖(⟪u, a⟫ - ⟪u, b⟫) • u‖
      = (⟪u, a⟫ - ⟪u, b⟫) ^ 2 := by
    rw [← pow_two, norm_smul, Real.norm_eq_abs, mul_pow, h2u, mul_one, sq_abs]
  have hpp1 : ⟪(Aa - Ab) • u, W⟫ = 0 := by rw [real_inner_smul_left, hperp, mul_zero]
  have hpp2 : ⟪(⟪u, a⟫ - ⟪u, b⟫) • u, W⟫ = 0 := by
    rw [real_inner_smul_left, hperp, mul_zero]
  have hgoal : ‖(Aa - Ab) • u + W‖ * ‖(Aa - Ab) • u + W‖
      ≤ ‖(⟪u, a⟫ - ⟪u, b⟫) • u + W‖ * ‖(⟪u, a⟫ - ⟪u, b⟫) • u + W‖ := by
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hpp1,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hpp2, hsq1, hsq2]
    linarith
  have hgoal2 : ‖(Aa - Ab) • u + W‖ ^ 2 ≤ ‖(⟪u, a⟫ - ⟪u, b⟫) • u + W‖ ^ 2 := by
    rw [pow_two, pow_two]
    exact hgoal
  rw [hgrad, hsub]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hgoal2
