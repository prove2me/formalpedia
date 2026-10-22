-- Prove2me | solution 1 for FullFormalization.gd_trajectory
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T07:08:43.655773+00:00
-- url     : https://prove2.me/submissions/518f73f2-d8ec-45b7-8296-39a3de2c7f1a

-- Generated from F:/20261008/FullFormalization\FullFormalization\CommonExtremizer.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.CommonExtremizer

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, sections 27-31:
  the common extremizer that gives the lower bound of Theorem B.

  The setting is section 23: `L = 1`, `R = 1`, `x_init = 0`, and the ambient
  space is `EuclideanSpace ℝ (Fin D)` with `D = 2N+1`.  Section 24 produces the
  unit *hidden direction* `u` (first `N` coordinates zero, orthogonal to every
  predetermined random-search query), and sections 25-26 build the extremal
  function

      f_N(z) = H_c(⟪u,z⟫ - 1) + (1/2)‖z - ⟪u,z⟫ u‖²,   c = 1/(2 d_N + 1),

  which is convex, differentiable, globally 1-smooth, with unique minimiser `u`
  and `f_N(u) = 0` (`LiftedHuber.lean`).  This file runs the five strategies on
  that one function:

  * (27) the rational-NAG iterates are `x_k = d_k c u` for `k ≤ N`, all in the
    Huber linear region `⟪u,x_k⟫ = d_k c ≤ d_N c < 1 - c`, and
    `q_{NAG,N}(f_N) = 1/(2(2 d_N+1)) = tau_N` — the *upper* bound is attained;
  * (28) GD with step `1/L = 1` outputs `N c u`, and
    `q_{GD,N} - tau_N = (d_N - N)/(2 d_N+1)²  ≥ 0`; half-GD outputs `(Nc/2) u`
    with `q_{halfGD,N} - tau_N = (d_N - N/2)/(2 d_N+1)² ≥ 0`;
  * (29) every fixed-seed query lies in `u^⊥`, so `f_N(q_i) = B_N + ½‖q_i‖² ≥ B_N`;
    the output is one of the queries, so `q_{rand,N} ≥ B_N > tau_N`;
  * (30) every grid-then-refine query touches only the first `N` coordinates,
    hence lies in `u^⊥`; `f_N(z) = B_N + ½‖z‖²` there, so the origin stays the
    incumbent through both phases — the decision logic is *proved*, not assumed —
    and `q_{grid,N} = B_N > tau_N`;
  * (31) the minimum of the five losses is therefore exactly `tau_N`: the
    portfolio value coincides with the NAG value on this single function.

  Everything is proved for an arbitrary unit `u` with vanishing first `N`
  coordinates and an arbitrary orthogonal query list, so the construction is
  uniform in `u`; `exists_extremizer` then produces such a `u` from
  `HiddenDirection.exists_unit_hidden_direction`, and `theoremB_sup_eq_tau`
  turns the result into the `sup = tau_N` statement given the universal upper
  bound of section 22 as a hypothesis.

  Nothing is postulated: no `sorry`, `admit`, `axiom` or `unsafe`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_CommonExtremizer
import Definitions.Def_FunctionClass
import Definitions.Def_GradientStrategies
import Definitions.Def_GridRefine
import Definitions.Def_HiddenDirection
import Definitions.Def_LiftedHuber
import Definitions.Def_PortfolioDefinitions
import Definitions.Def_RandomSearch
import Definitions.Def_RationalNAG
import Theorems.Thm_FullFormalization_GD_point_succ
import Theorems.Thm_FullFormalization_GD_point_zero
import Theorems.Thm_FullFormalization_GD_step_eq
import Theorems.Thm_FullFormalization_Hc_of_abs_le
import Theorems.Thm_FullFormalization_Hc_of_le_abs
import Theorems.Thm_FullFormalization_clip_eq_max
import Theorems.Thm_FullFormalization_clip_le_left
import Theorems.Thm_FullFormalization_clip_neg
import Theorems.Thm_FullFormalization_clip_pos
import Theorems.Thm_FullFormalization_clip_self
import Theorems.Thm_FullFormalization_d_nonneg
import Theorems.Thm_FullFormalization_descentPoint_succ
import Theorems.Thm_FullFormalization_gradient_liftedHuberWith
import Theorems.Thm_FullFormalization_gradient_liftedHuberWith_line
import Theorems.Thm_FullFormalization_gradient_liftedHuber_line
import Theorems.Thm_FullFormalization_hasDerivAt_Hc
import Theorems.Thm_FullFormalization_hasFDerivAt_Hc_inner
import Theorems.Thm_FullFormalization_hasFDerivAt_half_norm_sq
import Theorems.Thm_FullFormalization_hasFDerivAt_liftedHuberWith
import Theorems.Thm_FullFormalization_hasFDerivAt_orthProj
import Theorems.Thm_FullFormalization_inner_orthProj
import Theorems.Thm_FullFormalization_inner_orthProj_left
import Theorems.Thm_FullFormalization_inner_u_self
import Theorems.Thm_FullFormalization_le_d
import Theorems.Thm_FullFormalization_liftedHuber_c_pos
import Theorems.Thm_FullFormalization_nat_mul_c_le
import Theorems.Thm_FullFormalization_oracleOf_gradient
import Theorems.Thm_FullFormalization_orthProjL_apply
import Theorems.Thm_FullFormalization_two_d_add_one_pos

open scoped Gradient RealInnerProductSpace Topology
open Set

set_option linter.unusedSectionVars false

namespace FullFormalization

noncomputable section

/-! ### Scalars: the cutoff `c = 1/(2 d_N+1)` and the value `B_N` -/





















/-! ### The value of `f_N` on vectors orthogonal to `u`

`LiftedHuber.liftedHuber_eq` gives `f_N(z) = H_c(⟪u,z⟫-1) + ½‖z - ⟪u,z⟫u‖²`;
on `u^⊥` the first term is the constant `H_c(-1) = c - c²/2 = B_N` (26.5)-(26.6)
and the second is `½‖z‖²`. -/







/-! ### The hidden direction and the first-coordinate support

`HiddenDirection.exists_unit_hidden_direction` supplies `u` with `‖u‖ = 1`,
`u j = 0` for every coordinate `j` with `j < N`, and `⟪u, q i⟫ = 0` for every
predetermined query.  Vectors whose coordinates `≥ N` vanish are exactly the
vectors of the source's "first `N` coordinate directions", and they are all
orthogonal to `u`. -/















/-! ### Section 27: the NAG trajectory on the extremizer -/

















/-! ### Section 28: the two gradient-descent strategies -/

























/-! ### Section 29: fixed-seed random search -/











/-! ### Section 30: grid-then-refine -/



























/-! ### Section 31: the five algorithms combined -/























end

end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace Topology
open Set
set_option linter.unusedSectionVars false

open FullFormalization in

theorem solution (N : ℕ) (u : GridSpace N) (hu : ‖u‖ = 1) :
    ∀ k ≤ N, GD.point (oracleOf (liftedHuber u N)) 1 k = ((k : ℝ) * (1 / (2 * d N + 1))) • u := by
  intro k
  induction k with
  | zero => intro _; simp [GD.point_zero]
  | succ k ih =>
      intro hk
      have hk' : k ≤ N := by omega
      have hgrad : ∇ (liftedHuber u N) (((k : ℝ) * (1 / (2 * d N + 1))) • u)
          = -(1 / (2 * d N + 1)) • u :=
        gradient_liftedHuber_line u N hu (nat_mul_c_le N k hk')
      rw [GD_step_eq, ih hk', hgrad]
      rw [neg_smul, sub_neg_eq_add, ← add_smul]
      congr 1
      push_cast
      ring
