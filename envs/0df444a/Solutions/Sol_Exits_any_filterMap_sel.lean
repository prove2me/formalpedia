-- Prove2me | solution 1 for Exits.any_filterMap_sel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:59:03.74688+00:00
-- url     : https://prove2.me/submissions/cda6b3f3-ca42-486c-860a-dd656d43dd4d

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
variable (sel : τ → Option ν) (v : ν → Bool) (w : τ → Bool) (hw : ∀ x, w x = ((sel x).map v).getD false)
include hw
namespace Exits
theorem _root_.solution (xs : List τ) : (xs.filterMap sel).any v = xs.any w := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : sel x with
    | none => rw [List.filterMap_cons_none h, ih, List.any_cons, hw x, h]; rfl
    | some y => rw [List.filterMap_cons_some h, List.any_cons, ih, List.any_cons, hw x, h]; rfl
end Exits
