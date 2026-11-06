-- Prove2me | solution 2 for CircuitLowerBound.TabF.two_pow_size_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:35:09.158196+00:00
-- url     : https://prove2.me/submissions/e4c8f2dc-06ab-43c8-b339-8ea5a739de01

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Cert_Sched
import Definitions.Def_CircuitLowerBound_Small
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Cert_TabF
import Theorems.Thm_Groundwork_PolyT_congr


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.TabF
open ENP Groundwork Sched
variable {α : Type} [Enc α]
namespace CircuitLowerBound.TabF
theorem _root_.solution (n : ℕ) : 2 ^ Nat.size n ≤ 2 * n + 1 := by
  rcases Nat.eq_zero_or_pos (Nat.size n) with h | h
  · rw [h]; omega
  · have h1 : 2 ^ (Nat.size n - 1) ≤ n := Nat.lt_size.1 (by omega)
    have h2 : 2 ^ Nat.size n = 2 * 2 ^ (Nat.size n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
end CircuitLowerBound.TabF
