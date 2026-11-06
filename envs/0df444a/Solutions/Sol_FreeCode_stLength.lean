-- Prove2me | solution 1 for FreeCode.stLength
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:47:40.514322+00:00
-- url     : https://prove2.me/submissions/4e505ae7-fa56-424f-b1c5-35a59ca14730

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FreeCode_Code
import Theorems.Thm_FreeCode_length_enc_succ_le
import Theorems.Thm_Groundwork_DecodeK_length_enc_succ_le
import Theorems.Thm_Groundwork_Decode_length_enc_succ_le


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)
namespace FreeCode
theorem _root_.solution : StLength := fun k => ⟨2 ^ k * (k + 1) + 2, k + 1, fun _ _ h => length_enc_succ_le h⟩
end FreeCode
