-- Prove2me | solution 1 for ClauseBound.ParityChecks.RunF.runChecks_shape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:21:19.091527+00:00
-- url     : https://prove2.me/submissions/88760d48-80ab-43a3-8e69-ed7bde8fb4aa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Theorems.Thm_ClauseBound_ParityChecks_RunF_len_runTo_le
import Theorems.Thm_ClauseBound_ParityChecks_Run_runChecks_succ
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}
namespace ClauseBound.ParityChecks.RunF
theorem _root_.solution (j : ℕ) : (q.runChecks oA oB j).length = j ∧ ∀ L ∈ q.runChecks oA oB j, len L ≤ lenChk q.m := by
  induction j with
  | zero => exact ⟨rfl, fun L hL => absurd hL (List.not_mem_nil)⟩
  | succ j ih =>
    rw [runChecks_succ]
    refine ⟨by rw [List.length_append, ih.1]; rfl, fun L hL => ?_⟩
    rcases List.mem_append.1 hL with h | h
    · exact ih.2 L h
    · rw [List.mem_singleton.1 h]; exact len_runTo_le _ le_rfl
end ClauseBound.ParityChecks.RunF
