-- Prove2me | solution 1 for ClauseBound.ParityChecks.ArithOL.gPO_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:52:08.011292+00:00
-- url     : https://prove2.me/submissions/68b0f727-393c-4b15-9457-072ccdecd472

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_ArithR
import Definitions.Def_ClauseBound_TopN_Budget
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_ClauseBound_ParityChecks_ArithOL
import Theorems.Thm_ClauseBound_ParityChecks_ArithOL_two_le_D
import Theorems.Thm_ClauseBound_ParityChecks_LD_two_pow
import Theorems.Thm_ClauseBound_ParityChecks_clog_le_size
import Theorems.Thm_ClauseBound_ParityChecks_g_mul_PbOL_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith
variable {k K n s C₀ : ℕ}
namespace ClauseBound.ParityChecks.ArithOL
theorem _root_.solution (hn : 1 ≤ n) (hK8 : K ^ 8 ≤ n) :
    3 * K ^ 8 * PbOL K n (2 ^ betaN k s) ≤ 1330 * (2 * n) * 2 ^ betaN k s * (betaN k s + 1) * (betaN k s + 2 + n.size) := by
  have h := g_mul_PbOL_le hn (two_le_D k s) K
  rw [LD_two_pow] at h
  refine h.trans ?_
  have h1 := clog_le_size n
  exact Nat.mul_le_mul (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega)))) (by omega)
end ClauseBound.ParityChecks.ArithOL
