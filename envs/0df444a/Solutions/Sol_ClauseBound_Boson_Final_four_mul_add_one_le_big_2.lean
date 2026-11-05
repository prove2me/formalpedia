-- Prove2me | solution 2 for ClauseBound.Boson.Final.four_mul_add_one_le_big
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:33:12.18384+00:00
-- url     : https://prove2.me/submissions/104c4f10-2bb9-4532-b9a7-c4aca63c76ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Half
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_ClauseBound_Boson_Final

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Final
namespace ClauseBound.Boson.Final
theorem _root_.solution (h : ℕ) : 4 * h + 1 ≤ big h := by
  have : 4 * h + 1 ≤ 40 * (h + 1) ^ 2 := by nlinarith
  exact this.trans (Nat.le_add_right _ _)
end ClauseBound.Boson.Final
