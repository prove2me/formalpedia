-- Prove2me | solution 1 for ClauseBound.ParityChecks.Params.Big.i0_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:13:48.413946+00:00
-- url     : https://prove2.me/submissions/3f3b6817-227a-4901-b10a-30adf3975a04

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_n_ne
import Theorems.Thm_ClauseBound_ParityChecks_Params_Big_i0_spec

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
theorem _root_.solution : 1 ≤ i0Of n := by
  have h1 := b.i0_spec.1
  have h2 := b.n_ne
  rcases Nat.eq_zero_or_pos (i0Of n) with h | h
  · rw [h, mul_zero] at h1; omega
  · exact h
end ClauseBound.ParityChecks.Params.Big
