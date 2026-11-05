-- Prove2me | solution 1 for ClauseBound.ParityChecks.Count.getD_pad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:10:51.046767+00:00
-- url     : https://prove2.me/submissions/97ec2fde-5192-4a26-9e99-95577de0f1cb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_PaddedDescent_F_Eval
import Definitions.Def_ClauseBound_ParityChecks_Count
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.Count
open Finset Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Eval ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW _root_.ParityChecks
namespace ClauseBound.ParityChecks.Count
theorem _root_.solution (Lam : List Chk) (t j : ℕ) : (Lam ++ List.replicate t []).getD j [] = Lam.getD j [] := by
  rcases Nat.lt_or_ge j Lam.length with h | h
  · rw [List.getD_append _ _ _ _ h]
  · rw [List.getD_append_right _ _ _ _ h, List.getD_eq_default Lam _ h]
    rcases Nat.lt_or_ge (j - Lam.length) t with h' | h'
    · rw [List.getD_eq_getElem _ _ (by rw [List.length_replicate]; exact h'), List.getElem_replicate]
    · rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; exact h')]
end ClauseBound.ParityChecks.Count
