-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.poly_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:14:46.792313+00:00
-- url     : https://prove2.me/submissions/310ea38a-770d-4ca7-ab60-d82914425f84

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_t_pos
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_succ_le
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big___le_dae0589ea56c
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_LD_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params
open ClauseBound.ParityChecks.Params.Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b
namespace ClauseBound.ParityChecks.Params.Big
theorem _root_.solution : 12 * Δ * LD Δ * ℓ ≤ 2 ^ (ℓ / 2) := by
  have h1 := b.Δ_le
  have h2 : LD Δ ≤ 2 ^ (c * t) := le_trans b.LD_le (by rw [add_comm]; exact Nat.lt_two_pow_self)
  have h3 : ℓ ≤ 2 ^ t := by have := b.succ_le; omega
  have h4 : 4 + c * t + c * t + t ≤ ℓ / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have := b.hA'; have := b.t_pos; omega
  calc 12 * Δ * LD Δ * ℓ ≤ 2 ^ 4 * 2 ^ (c * t) * 2 ^ (c * t) * 2 ^ t := by gcongr; norm_num
    _ = 2 ^ (4 + c * t + c * t + t) := by rw [pow_add, pow_add, pow_add]
    _ ≤ 2 ^ (ℓ / 2) := Nat.pow_le_pow_right (by norm_num) h4
end ClauseBound.ParityChecks.Params.Big
