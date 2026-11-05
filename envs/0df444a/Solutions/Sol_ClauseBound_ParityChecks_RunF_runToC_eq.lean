-- Prove2me | solution 1 for ClauseBound.ParityChecks.RunF.runToC_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:19:48.316047+00:00
-- url     : https://prove2.me/submissions/8c254de0-89b5-4ee9-84b8-85681022cbb9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Theorems.Thm_ClauseBound_ParityChecks_RunF_len_runTo_le
import Theorems.Thm_ClauseBound_ParityChecks_Run_runTo_succ
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
theorem _root_.solution (hp : lenChk q.m ≤ pad.length) (Ls : List Chk) {e : ℕ} (he : e ≤ q.m) : runToC pad q oA oB Ls e = q.runTo oA oB Ls e := by
  induction e with
  | zero => exact cap_eq ((len_runTo_le (q := q) (oA := oA) (oB := oB) Ls (Nat.zero_le _)).trans hp)
  | succ e ih =>
    have e1 : runToC pad q oA oB Ls (e + 1) = cap pad [] (q.decide1 oA oB Ls (runToC pad q oA oB Ls e) e) := by
      unfold runToC
      rw [List.range_succ, List.foldl_append]
      rfl
    rw [e1, ih (by omega), ← runTo_succ]
    exact cap_eq ((len_runTo_le Ls he).trans hp)
end ClauseBound.ParityChecks.RunF
