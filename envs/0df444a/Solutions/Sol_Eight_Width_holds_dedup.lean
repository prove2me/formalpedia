-- Prove2me | solution 1 for Eight.Width.holds_dedup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:27:50.853302+00:00
-- url     : https://prove2.me/submissions/98cf6bc6-5d57-46a2-9dd4-c143744bc4a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
variable {n : ℕ}
namespace Eight.Width
theorem _root_.solution {W : Type} [DecidableEq W] {a : W → Bool} {φ : List (List (W × Bool))} : Holds a φ.dedup ↔ Holds a φ := by
  simp [Holds]
end Eight.Width
