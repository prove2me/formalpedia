-- Prove2me | solution 1 for Eight.ViaGrouping.stLevelKeepsP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:53:26.110743+00:00
-- url     : https://prove2.me/submissions/60dff9c6-6dbd-435e-b2f4-704bd7c5e2cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Level
import Definitions.Def_Eight_ViaGrouping_LevelCert
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Theorems.Thm_Eight_ViaGrouping_stLevelKeepsP_of
import Theorems.Thm_Eight_stKeeps


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution : StLevelKeepsP := stLevelKeepsP_of stKeeps
end Eight.ViaGrouping
