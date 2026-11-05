-- Prove2me | solution 1 for Exits.tested_append_of_fail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:57:33.694799+00:00
-- url     : https://prove2.me/submissions/bf18b7d7-0c2a-4d43-b619-a122d1bc707a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Defs
import Definitions.Def_Exits_Tested
import Theorems.Thm_Exits_tested_cons_of_fail

set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Stepped
variable {α β γ τ ν : Type}
namespace Exits
theorem _root_.solution {v : ν → Bool} {A : List ν} (h : A.any v = false) (B : List ν) : tested v (A ++ B) = A ++ tested v B := by
  induction A with
  | nil => rfl
  | cons x A ih =>
    rw [List.any_cons, Bool.or_eq_false_iff] at h
    rw [List.cons_append, tested_cons_of_fail h.1, ih h.2, List.cons_append]
end Exits
