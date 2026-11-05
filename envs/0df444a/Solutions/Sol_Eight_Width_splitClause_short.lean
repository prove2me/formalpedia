-- Prove2me | solution 1 for Eight.Width.splitClause_short
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:35:03.98699+00:00
-- url     : https://prove2.me/submissions/903d0819-4bd1-43dc-b76c-5782bbf4d38b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Cor_WidthDefs
import Mathlib.Tactic
import Definitions.Def_Eight_Cor_Width
import Theorems.Thm_Eight_Width_splitClause_nil

set_option autoImplicit false
section
section
open Eight Eight.Width
open Sat3 (Lit CNF)
variable {V : Type}
namespace Eight.Width
theorem _root_.solution (ys : List V) {C : List (V × Bool)} (h : C.length ≤ 3) : splitClause ys C = [C] := by
  match ys, C, h with
  | [], _, _ => exact splitClause_nil _
  | _ :: _, [], _ => rfl
  | _ :: _, [_], _ => rfl
  | _ :: _, [_, _], _ => rfl
  | _ :: _, [_, _, _], _ => rfl
  | _ :: _, _ :: _ :: _ :: _ :: _, h => simp at h; omega
end Eight.Width
