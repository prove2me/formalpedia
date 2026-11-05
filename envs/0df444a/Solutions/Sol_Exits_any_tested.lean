-- Prove2me | solution 1 for Exits.any_tested
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:33:58.745085+00:00
-- url     : https://prove2.me/submissions/7030d20c-594c-4f2e-a828-ea4846ec80d4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_Defs
import Definitions.Def_Exits_Tested
set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Stepped
variable {α β γ τ ν : Type}

theorem solution (v : ν → Bool) (l : List ν) : (tested v l).any v = l.any v := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases h : v a with
    | false =>
      change (List.take ((a :: l).findIdx v + 1) (a :: l)).any v = (a :: l).any v
      rw [List.findIdx_cons]
      simp only [h, List.take_succ_cons, List.any_cons, Bool.false_or]
      exact ih
    | true =>
      simp [Exits.tested, List.findIdx_cons, h]
