-- Prove2me | solution 1 for Exits.reach_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:59:02.691945+00:00
-- url     : https://prove2.me/submissions/40697919-02ec-4278-8352-2f85f993048f

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
namespace Exits
theorem _root_.solution (q : ℕ → Bool) (n : ℕ) : reach q n ≤ n := by
  unfold reach
  cases h : (List.range n).find? q with
  | none => exact le_rfl
  | some i => exact List.mem_range.1 (List.mem_of_find?_eq_some h)
end Exits
