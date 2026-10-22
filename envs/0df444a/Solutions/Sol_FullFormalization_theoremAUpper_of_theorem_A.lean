-- Prove2me | solution 1 for FullFormalization.theoremAUpper_of_theorem_A
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T07:41:42.333497+00:00
-- url     : https://prove2.me/submissions/58a821f7-4761-41d4-8810-4cab16262368

-- Generated from F:/20261008/FullFormalization\FullFormalization\MainResults.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.MainResults

  Assembles the two headline results of the source document from the files that
  prove their halves, with **no hypothesis left standing in for a theorem**.

    * Theorem A — `auditable_full_proof_nag_and_five_algorithm_cn.md`, §17-§20:
      `TheoremA.theorem_A_upper`, `TheoremA.theorem_A_sup`;
    * Theorem B — §21-§32: `TheoremB.theoremB`, which up to now carried
      `TheoremAUpper N (GridSpace N)` as an explicit hypothesis because
      `TheoremA.lean` did not yet exist.

  This file supplies that hypothesis from `TheoremA.theorem_A_upper` and
  restates Theorem B without it.  Nothing is weakened: `TheoremAUpper` was
  always exactly the statement of Theorem A in the vocabulary of the portfolio
  file, and `TheoremB.theoremB`'s own docstring says so.
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
import Definitions.Def_Huber1D
import Definitions.Def_LiftedHuber
import Definitions.Def_NAGUpperBound
import Definitions.Def_PortfolioDefinitions
import Definitions.Def_Positivity
import Definitions.Def_RandomSearch
import Definitions.Def_RationalNAG
import Definitions.Def_Scaling
import Definitions.Def_TheoremA
import Definitions.Def_TheoremB
import Theorems.Thm_FullFormalization_D_diff
import Theorems.Thm_FullFormalization_D_diff_prime
import Theorems.Thm_FullFormalization_D_ne_zero
import Theorems.Thm_FullFormalization_D_pos
import Theorems.Thm_FullFormalization_D_succ
import Theorems.Thm_FullFormalization_D_zero_capital
import Theorems.Thm_FullFormalization_H_last_eq_d
import Theorems.Thm_FullFormalization_H_last_eq_d_prime
import Theorems.Thm_FullFormalization_H_pos_capital
import Theorems.Thm_FullFormalization_H_sub_H_pred
import Theorems.Thm_FullFormalization_H_sub_H_pred_prime
import Theorems.Thm_FullFormalization_H_zero
import Theorems.Thm_FullFormalization_Ival_nonneg
import Theorems.Thm_FullFormalization_Pbeta_pos
import Theorems.Thm_FullFormalization_Qbeta_pos
import Theorems.Thm_FullFormalization_a_eq
import Theorems.Thm_FullFormalization_a_last
import Theorems.Thm_FullFormalization_a_pos
import Theorems.Thm_FullFormalization_alpha_pos
import Theorems.Thm_FullFormalization_b_eq
import Theorems.Thm_FullFormalization_b_last_eq
import Theorems.Thm_FullFormalization_b_pos
import Theorems.Thm_FullFormalization_b_zero
import Theorems.Thm_FullFormalization_betaT_eq
import Theorems.Thm_FullFormalization_betaT_num_shift
import Theorems.Thm_FullFormalization_betaT_pos
import Theorems.Thm_FullFormalization_beta_eq_P
import Theorems.Thm_FullFormalization_beta_pos
import Theorems.Thm_FullFormalization_boundary_N_eq_one
import Theorems.Thm_FullFormalization_boundary_bound
import Theorems.Thm_FullFormalization_comp_smul_one
import Theorems.Thm_FullFormalization_convexOn_le_gradient
import Theorems.Thm_FullFormalization_d_mono
import Theorems.Thm_FullFormalization_d_nonneg
import Theorems.Thm_FullFormalization_d_one
import Theorems.Thm_FullFormalization_d_sub_pred
import Theorems.Thm_FullFormalization_d_succ_sub
import Theorems.Thm_FullFormalization_d_zero
import Theorems.Thm_FullFormalization_descent_lemma
import Theorems.Thm_FullFormalization_differentiable_inner_const
import Theorems.Thm_FullFormalization_differentiable_scaled
import Theorems.Thm_FullFormalization_endpoint_identity
import Theorems.Thm_FullFormalization_gradient_add_const
import Theorems.Thm_FullFormalization_gradient_congr
import Theorems.Thm_FullFormalization_gradient_const_add
import Theorems.Thm_FullFormalization_gradient_inner_const
import Theorems.Thm_FullFormalization_gradient_normalized
import Theorems.Thm_FullFormalization_gradient_scaled
import Theorems.Thm_FullFormalization_gradient_sub
import Theorems.Thm_FullFormalization_gradient_sub_inner
import Theorems.Thm_FullFormalization_h_at_N
import Theorems.Thm_FullFormalization_h_last
import Theorems.Thm_FullFormalization_h_last_prime
import Theorems.Thm_FullFormalization_h_pos
import Theorems.Thm_FullFormalization_h_rec
import Theorems.Thm_FullFormalization_hasFDerivAt_scaledArg
import Theorems.Thm_FullFormalization_initial_identity
import Theorems.Thm_FullFormalization_interior_identity
import Theorems.Thm_FullFormalization_mom_zero
import Theorems.Thm_FullFormalization_nagX_succ
import Theorems.Thm_FullFormalization_nagX_succ_prime
import Theorems.Thm_FullFormalization_nagX_zero
import Theorems.Thm_FullFormalization_nagY_succ
import Theorems.Thm_FullFormalization_nagY_succ_one
import Theorems.Thm_FullFormalization_nagY_zero
import Theorems.Thm_FullFormalization_nag_upper_bound_normalized
import Theorems.Thm_FullFormalization_scaledArg_add_smul
import Theorems.Thm_FullFormalization_scaledArg_apply
import Theorems.Thm_FullFormalization_scaled_apply
import Theorems.Thm_FullFormalization_tau_eq_inv
import Theorems.Thm_FullFormalization_tau_one
import Theorems.Thm_FullFormalization_tau_pos
import Theorems.Thm_FullFormalization_telescope
import Theorems.Thm_FullFormalization_terminal_identity
import Theorems.Thm_FullFormalization_theorem_A_upper
import Theorems.Thm_FullFormalization_toDual_smul_real
import Theorems.Thm_FullFormalization_two_d_add_one

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]







end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

open FullFormalization in

theorem solution (N : ℕ) (hN : 1 ≤ N) : TheoremAUpper N E := by
  intro L R f x_init xstar hR A
  have hb := theorem_A_upper A hR N hN
  have hden : (0 : ℝ) < L * R ^ 2 := by
    have hL : 0 < L := A.L_pos
    positivity
  have hdiv : (f (nagX f L x_init N) - f xstar) / (L * R ^ 2)
      ≤ (2 * L * R ^ 2 / ((N : ℝ) ^ 2 + 7 * (N : ℝ) + 4)) / (L * R ^ 2) :=
    div_le_div_of_nonneg_right hb (le_of_lt hden)
  have h1 : L * R ^ 2 ≠ 0 := ne_of_gt hden
  have h2 : ((N : ℝ) ^ 2 + 7 * (N : ℝ) + 4) ≠ 0 := by positivity
  have hsimp : (2 * L * R ^ 2 / ((N : ℝ) ^ 2 + 7 * (N : ℝ) + 4)) / (L * R ^ 2)
      = tau N := by
    rw [tau]
    field_simp
    exact mul_inv_cancel₀ (ne_of_gt A.L_pos)

  rw [qLoss]
  exact hdiv.trans (le_of_eq hsimp)
