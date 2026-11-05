-- Prove2me | solution 1 for ClauseBound.ParityChecks.RunF.runC_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:36:22.817373+00:00
-- url     : https://prove2.me/submissions/4e3548b5-9bce-4144-9157-61601237758a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Theorems.Thm_ClauseBound_ParityChecks_RunF_runToC_eq
import Theorems.Thm_ClauseBound_ParityChecks_RunF_len_runChecks_le
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
import Theorems.Thm_ClauseBound_ParityChecks_Run_runChecks_succ
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_PaddedDescent_F_cap_eq
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}
namespace ClauseBound.ParityChecks.RunF
theorem _root_.solution (hp : q.r * (lenChk q.m + 2) + 2 ≤ pad.length) (hp' : lenChk q.m ≤ pad.length) : runC pad q oA oB = q.run oA oB := by
  have key : ∀ j ≤ q.r, (List.range j).foldl (fun Ls _ => cap pad [] (Ls ++ [runToC pad q oA oB Ls q.m])) (cap pad [] []) = q.runChecks oA oB j := by
    intro j
    induction j with
    | zero => exact fun _ => cap_eq ((len_runChecks_le (q := q) (oA := oA) (oB := oB) (Nat.zero_le _)).trans hp)
    | succ j ih =>
      intro hj
      rw [List.range_succ, List.foldl_append, ih (by omega)]
      change cap pad [] (q.runChecks oA oB j ++ [runToC pad q oA oB (q.runChecks oA oB j) q.m]) = _
      rw [runToC_eq hp' _ le_rfl, ← runChecks_succ]
      exact cap_eq ((len_runChecks_le hj).trans hp)
  exact key q.r le_rfl
end ClauseBound.ParityChecks.RunF
