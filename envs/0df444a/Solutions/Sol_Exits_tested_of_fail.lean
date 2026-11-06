-- Prove2me | solution 1 for Exits.tested_of_fail
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:25:01.917747+00:00
-- url     : https://prove2.me/submissions/9d21f964-5964-4c3c-9184-f14f9c2ff98e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Defs
import Definitions.Def_Exits_Tested
import Theorems.Thm_Exits_tested_nil
import Theorems.Thm_Exits_tested_cons_of_fail

set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Stepped
variable {α β γ τ ν : Type}
namespace Exits
theorem _root_.solution {v : ν → Bool} {l : List ν} (h : l.any v = false) : tested v l = l := by
  induction l with
  | nil => exact tested_nil v
  | cons x l ih =>
    rw [List.any_cons, Bool.or_eq_false_iff] at h
    rw [tested_cons_of_fail h.1, ih h.2]
end Exits
