-- Prove2me | solution 1 for Eight.one_add_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:48:31.690241+00:00
-- url     : https://prove2.me/submissions/eb0c9a36-aa02-47e4-a0c9-5cb6fd8fdaa9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eight_SecCrossing_Identity
import Theorems.Thm_Eight_exists_bit

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {d : Block} (h : d ≠ (false, false, false)) :
    1 + (1 + d.1.toNat) * (1 + d.2.1.toNat) * (1 + d.2.2.toNat) ≡ 1 [MOD 2] := by
  have e : ∃ n, (1 + d.1.toNat) * (1 + d.2.1.toNat) * (1 + d.2.2.toNat) = 2 * n := by
    rcases exists_bit h with h1 | h1 | h1
    · exact ⟨(1 + d.2.1.toNat) * (1 + d.2.2.toNat), by rw [h1, Bool.toNat_true]; ring⟩
    · exact ⟨(1 + d.1.toNat) * (1 + d.2.2.toNat), by rw [h1, Bool.toNat_true]; ring⟩
    · exact ⟨(1 + d.1.toNat) * (1 + d.2.1.toNat), by rw [h1, Bool.toNat_true]; ring⟩
  obtain ⟨n, hn⟩ := e
  rw [hn]
  unfold Nat.ModEq
  omega
end Eight
