-- Prove2me | solution 1 for ClauseBound.TopN.Arith.b_le_D
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:35:31.837196+00:00
-- url     : https://prove2.me/submissions/083f6d1f-9558-4af7-a72d-d1261912c7f2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_TopN_Budget
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_ClauseBound_TopN_Arith

set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Arith
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith
variable {k K n s : ℕ}
namespace ClauseBound.TopN.Arith
theorem _root_.solution (k s : ℕ) : betaN k s + 3 ≤ 2 ^ betaN k s := by
  have h3 : 3 ≤ betaN k s := by unfold betaN; omega
  obtain ⟨t, ht⟩ : ∃ t, betaN k s = t + 3 := ⟨betaN k s - 3, by omega⟩
  have h : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
  rw [ht, pow_add]
  omega
end ClauseBound.TopN.Arith
