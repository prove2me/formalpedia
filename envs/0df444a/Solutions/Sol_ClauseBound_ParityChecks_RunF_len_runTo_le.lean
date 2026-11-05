-- Prove2me | solution 1 for ClauseBound.ParityChecks.RunF.len_runTo_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:15:29.812204+00:00
-- url     : https://prove2.me/submissions/43e488f9-3f39-4b2c-816e-c57beb63c37a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Theorems.Thm_ClauseBound_ParityChecks_RunF_runTo_shape
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_PaddedDescent_F_Lists_len_list_le__7630c2814a7f


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}
namespace ClauseBound.ParityChecks.RunF
theorem _root_.solution (Ls : List Chk) {e : ℕ} (he : e ≤ q.m) : len (q.runTo oA oB Ls e) ≤ lenChk q.m := by
  obtain ⟨h1, h2⟩ := runTo_shape (q := q) (oA := oA) (oB := oB) Ls e
  refine Lists.len_list_le' _ (3 * Nat.size q.m + 4) (h1.trans he) fun x hx => ?_
  have := Nat.size_le_size ((h2 x hx).le.trans he)
  rw [len_nat]
  omega
end ClauseBound.ParityChecks.RunF
