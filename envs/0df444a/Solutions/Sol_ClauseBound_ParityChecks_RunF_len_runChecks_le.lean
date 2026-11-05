-- Prove2me | solution 1 for ClauseBound.ParityChecks.RunF.len_runChecks_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:28:57.843277+00:00
-- url     : https://prove2.me/submissions/85933d6d-45d7-4a58-a39e-56aa6a520d8f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Theorems.Thm_ClauseBound_ParityChecks_RunF_runChecks_shape
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
theorem _root_.solution {j : ℕ} (hj : j ≤ q.r) : len (q.runChecks oA oB j) ≤ q.r * (lenChk q.m + 2) + 2 := by
  obtain ⟨h1, h2⟩ := runChecks_shape (q := q) (oA := oA) (oB := oB) j
  exact Lists.len_list_le' _ (lenChk q.m + 2) (h1.le.trans hj) fun L hL => Nat.add_le_add_right (h2 L hL) 2
end ClauseBound.ParityChecks.RunF
