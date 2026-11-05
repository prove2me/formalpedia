-- Prove2me | solution 1 for ClauseBound.ParityChecks.RunF.runTo_shape
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:09:07.939363+00:00
-- url     : https://prove2.me/submissions/d97e5664-47c0-443b-a66d-d45003aa3f38

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Theorems.Thm_ClauseBound_ParityChecks_Run_runTo_succ
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}
namespace ClauseBound.ParityChecks.RunF
theorem _root_.solution (Ls : List Chk) (e : ℕ) : (q.runTo oA oB Ls e).length ≤ e ∧ ∀ x ∈ q.runTo oA oB Ls e, x < e := by
  induction e with
  | zero => exact ⟨le_rfl, fun x hx => absurd hx (List.not_mem_nil)⟩
  | succ e ih =>
    rw [runTo_succ]
    unfold Par.decide1
    split_ifs
    · refine ⟨by rw [List.length_append, List.length_singleton]; omega, fun x hx => ?_⟩
      rcases List.mem_append.1 hx with h | h
      · exact (ih.2 x h).trans (Nat.lt_succ_self e)
      · rw [List.mem_singleton.1 h]; exact Nat.lt_succ_self e
    · exact ⟨ih.1.trans (Nat.le_succ e), fun x hx => (ih.2 x hx).trans (Nat.lt_succ_self e)⟩
end ClauseBound.ParityChecks.RunF
