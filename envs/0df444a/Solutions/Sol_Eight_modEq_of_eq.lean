-- Prove2me | solution 1 for Eight.modEq_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:42:05.019331+00:00
-- url     : https://prove2.me/submissions/95c97c75-5e48-44ce-ac6b-66925d166828

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

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {a b : ℕ} (h : a = b) : a ≡ b [MOD 2] := h ▸ Nat.ModEq.rfl
end Eight
