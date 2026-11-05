-- Prove2me | solution 1 for ClauseBound.ParityChecks.ArithOL.UbO_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:34:39.959939+00:00
-- url     : https://prove2.me/submissions/d3b61577-f9f7-44df-b4c9-5a87594da495

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
import Theorems.Thm_ClauseBound_ParityChecks_UbOL_le
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.ArithOL
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith
variable {k K n s C₀ : ℕ}
namespace ClauseBound.ParityChecks.ArithOL
theorem _root_.solution (hn : 1 ≤ n) : UbOL k K n (2 ^ betaN k s) ≤ 354 * k * n * (betaN k s + 1) + 54 * K ^ 16 := by
  have h := UbOL_le hn (two_le_D k s) k K
  rw [LD_two_pow] at h
  calc UbOL k K n (2 ^ betaN k s) ≤ 354 * k * n * (betaN k s + 1) + 6 * (3 * K ^ 8) ^ 2 := h
    _ = 354 * k * n * (betaN k s + 1) + 54 * K ^ 16 := by ring
end ClauseBound.ParityChecks.ArithOL
