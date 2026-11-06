-- Prove2me | solution 1 for CircuitLowerBound.Clause.Ew_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:37:13.933685+00:00
-- url     : https://prove2.me/submissions/6854c0fb-9dac-4daf-b6a3-0e09ef35dfc8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_CircuitLowerBound_Blocks_prevW_lt


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
namespace CircuitLowerBound.Clause
theorem _root_.solution (n rb : ℕ) {R k : ℕ} (hk : k < R) : Ew n rb k < n + 2 + rb * R := by
  have h1 : Ew n rb k < n + 2 + rb * k + rb := prevW_lt (by omega)
  have h2 : rb * (k + 1) ≤ rb * R := Nat.mul_le_mul_left _ hk
  rw [Nat.mul_succ] at h2
  omega
end CircuitLowerBound.Clause
