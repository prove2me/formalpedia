-- Prove2me | solution 1 for Exits.zero_lt_levelG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:43:26.277293+00:00
-- url     : https://prove2.me/submissions/5f955d5d-345b-4534-9097-f381b59feb76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_SecLevel_EStar
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic.Ring
import Definitions.Def_Exits_Level
import Theorems.Thm_Paper_levelK_ge


set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Paper Eight Eight.SecNetworks Eight.ViaGrouping
namespace Exits
theorem _root_.solution (ℓ : ℕ) : 0 < levelG ℓ := Nat.mul_pos (by norm_num) (Nat.pow_pos (lt_of_lt_of_le (by norm_num) (levelK_ge ℓ)))
end Exits
