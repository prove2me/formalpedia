-- Prove2me | solution 1 for Eight.Width.splitClause_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:30:27.692376+00:00
-- url     : https://prove2.me/submissions/92583726-2e7b-4808-8b21-51e4d6fcf070

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
theorem _root_.solution (y : V) (ys : List V) (l₁ l₂ l₃ l₄ : V × Bool) (r : List (V × Bool)) :
    splitClause (y :: ys) (l₁ :: l₂ :: l₃ :: l₄ :: r) = forced y l₁ l₂ ++ splitClause ys ((y, true) :: l₃ :: l₄ :: r) := rfl
end Eight.Width
