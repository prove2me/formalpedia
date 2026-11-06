-- Prove2me | solution 1 for ClausesOccur.allOccurOfUnary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:21:13.541447+00:00
-- url     : https://prove2.me/submissions/9e1cfd22-eb5e-4a41-a4eb-c1b09f192d4f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClausesOccurStatement
import Definitions.Def_OccurM_ArithBack
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ClauseBound_Alg_End
import Definitions.Def_OccurM_AllOccur
import Theorems.Thm_ClauseBound_Alg_End_length_enc_succ_le
import Theorems.Thm_ClauseBound_Alg_End_n_le
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le
import Theorems.Thm_Groundwork_Prog_NetE_n_le
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_OccurM_back_le
import Theorems.Thm_VariableBound_Rename_allOccurStmt


set_option autoImplicit false
section
section
open ClausesOccur
open Turing MainTheoremForms
open Sat3 (CNF)
namespace ClausesOccur
theorem _root_.solution : AllOccurOfUnaryStmt := by
  intro α h0 h1 M C hM
  refine ⟨650 * C + 1, fun k n φ hk hm hφ ho => ?_⟩
  obtain ⟨e1, e2⟩ := VariableBound.Rename.allOccurStmt n φ ho
  have h := hM k n φ hk hφ hm
  unfold CountsOccWithin at h
  rw [e1, e2] at h
  obtain ⟨ev⟩ := h
  have hl := ClauseBound.Alg.End.length_enc_succ_le hk (by omega) (ClauseBound.Alg.End.n_le hφ ho)
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (OccurM.back_le h0 h1 C hk hm (by omega))⟩⟩
end ClausesOccur
