-- Prove2me | solution 1 for ClauseBound.ParityChecks.RunF.lenChk_add_two_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:12:29.784221+00:00
-- url     : https://prove2.me/submissions/7fd51659-c76e-42bf-9d61-eec33b683f62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_Run
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_ClauseBound_ParityChecks_RunF

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.RunF
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.ParityChecks.Run
variable (pad : U) (q : Par) (oA : List Chk → ℤ) (oB : List Chk → Chk → ℕ → ℕ → ℤ)
variable {pad q oA oB}
namespace ClauseBound.ParityChecks.RunF
theorem _root_.solution {n Δ : ℕ} (hm : q.m ≤ Δ * n) : lenChk q.m + 2 ≤ 8 * ((Δ * n + 1) * (Nat.size (Δ * n) + 2)) := by
  have hs := Nat.size_le_size hm
  unfold lenChk
  have h2 : q.m * (3 * Nat.size q.m + 4) ≤ (Δ * n) * (3 * Nat.size (Δ * n) + 4) := Nat.mul_le_mul hm (by omega)
  nlinarith
end ClauseBound.ParityChecks.RunF
