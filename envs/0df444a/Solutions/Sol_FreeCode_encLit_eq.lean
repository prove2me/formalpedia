-- Prove2me | solution 1 for FreeCode.encLit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:24:36.22717+00:00
-- url     : https://prove2.me/submissions/41d2e28b-3f37-4c8d-89f8-8cd4c565be2d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FreeCode_Code
import Theorems.Thm_FreeCode_toWord_eq
import Theorems.Thm_Groundwork_Decode_toWord_eq


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)
namespace FreeCode
theorem _root_.solution {n : ℕ} (l : Lit n) : SatFree.encLit l = toWord (Nat.log2 (2 * n) + 1) (slot (some l)) := by
  rw [toWord_eq, SatFree.encLit]
end FreeCode
