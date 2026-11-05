-- Prove2me | solution 1 for Eight.Width.holds_append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:28:01.219462+00:00
-- url     : https://prove2.me/submissions/7cd9a227-3a3f-49c9-9044-70051bf37b2d

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
namespace Eight.Width
theorem _root_.solution {a : V → Bool} {φ ψ : List (List (V × Bool))} : Holds a (φ ++ ψ) ↔ Holds a φ ∧ Holds a ψ := by
  simp [Holds, or_imp, forall_and]
end Eight.Width
