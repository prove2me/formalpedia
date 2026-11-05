-- Prove2me | solution 1 for ClauseBound.ParityChecks.Binom.clog_le_logb_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:18:11.411949+00:00
-- url     : https://prove2.me/submissions/142898ca-bbbd-4a33-b520-91cc8741ec64

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Binom

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open ClauseBound.ParityChecks.Binom
namespace ClauseBound.ParityChecks.Binom
theorem _root_.solution {x : ℕ} (hx : 1 ≤ x) : (Nat.clog 2 x : ℝ) ≤ Real.logb 2 x + 1 := by
  have h0 : 0 ≤ Real.logb 2 (x : ℝ) := Real.logb_nonneg (by norm_num) (by exact_mod_cast hx)
  have h1 := Real.natCeil_logb_natCast 2 x
  have h2 := Nat.ceil_lt_add_one h0
  rw [← h1]
  exact_mod_cast h2.le
end ClauseBound.ParityChecks.Binom
