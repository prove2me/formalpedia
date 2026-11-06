-- Prove2me | solution 1 for Eight.ViaGrouping.stLevelP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:04:25.849245+00:00
-- url     : https://prove2.me/submissions/04cb16a1-30c9-451c-85e5-f943d3283554

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Level
import Definitions.Def_Eight_ViaGrouping_LevelCert
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Theorems.Thm_Eight_Level_stPresents_of
import Theorems.Thm_Eight_ViaGrouping_stLevelP_of
import Theorems.Thm_Eight_stPieces


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution : StLevelP := stLevelP_of (stPresents_of stPieces)
end Eight.ViaGrouping
