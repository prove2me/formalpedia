-- Prove2me | solution 1 for ClauseBound.ParityChecks.RunF.lenChk_le_big
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:09:08.99298+00:00
-- url     : https://prove2.me/submissions/de81eb26-9979-4750-b6f8-16358ef8cd25

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF
import Theorems.Thm_ClauseBound_ParityChecks_RunF_lenChk_add_two_le
import Theorems.Thm_ClauseBound_ParityChecks_RunF_big_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}
namespace ClauseBound.ParityChecks.RunF
theorem _root_.solution {n Δ : ℕ} (hm : q.m ≤ Δ * n) : lenChk q.m ≤ 8 * (6 * n + 1) * (Δ * n + 1) * (Nat.size (Δ * n) + 2) + 8 := by
  have h1 := lenChk_add_two_le (q := q) hm
  rw [big_eq]
  omega
end ClauseBound.ParityChecks.RunF
