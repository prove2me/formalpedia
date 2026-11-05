-- Prove2me | solution 1 for Exits.stLevelAchievableOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:32:55.283194+00:00
-- url     : https://prove2.me/submissions/c78cbf57-03f8-4b44-aafc-914886edd9a6

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

set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Paper Eight Eight.SecNetworks Eight.ViaGrouping
namespace Exits
theorem _root_.solution : StLevelAchievableOf := fun h K e hK h0 ⟨E, hk, hc⟩ => ⟨levelUp K E, (h K e E hK h0 hk hc).1, (h K e E hK h0 hk hc).2⟩
end Exits
