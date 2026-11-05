-- Prove2me | solution 1 for Exits.two_le_levelK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:40:29.791576+00:00
-- url     : https://prove2.me/submissions/928420e3-ad9b-4b13-9fab-a5303b0950c3

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
theorem _root_.solution (ℓ : ℕ) : 2 ≤ levelK ℓ := le_trans (by norm_num) (levelK_ge ℓ)
end Exits
