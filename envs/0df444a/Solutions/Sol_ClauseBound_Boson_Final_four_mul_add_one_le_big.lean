-- Prove2me | solution 1 for ClauseBound.Boson.Final.four_mul_add_one_le_big
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:09:21.473375+00:00
-- url     : https://prove2.me/submissions/2310e0fa-b5ae-4145-abda-a5a578dc43a3

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

theorem solution (h : ℕ) : 4 * h + 1 ≤ big h := by
  have : 4 * h + 1 ≤ 40 * (h + 1) ^ 2 := by nlinarith
  exact this.trans (Nat.le_add_right _ _)
