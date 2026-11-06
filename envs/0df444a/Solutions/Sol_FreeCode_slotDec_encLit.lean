-- Prove2me | solution 1 for FreeCode.slotDec_encLit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:36:43.794302+00:00
-- url     : https://prove2.me/submissions/0d947d5b-c534-40d6-a72a-606d3a010fa4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FreeCode_Code
import Theorems.Thm_FreeCode_slot_lt
import Theorems.Thm_FreeCode_slotDec_slot
import Theorems.Thm_FreeCode_encLit_eq
import Theorems.Thm_Groundwork_Decode_slotDec_slot
import Theorems.Thm_Groundwork_Decode_slot_lt
import Theorems.Thm_Groundwork_ofWord_toWord


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)
namespace FreeCode
theorem _root_.solution {n : ℕ} (l : Lit n) : slotDec (ofWord (SatFree.encLit l)) = some (l.1.val, l.2) := by
  rw [encLit_eq, ofWord_toWord (slot_lt l), slotDec_slot]
end FreeCode
