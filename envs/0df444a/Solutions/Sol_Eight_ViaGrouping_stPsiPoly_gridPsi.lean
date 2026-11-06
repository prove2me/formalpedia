-- Prove2me | solution 1 for Eight.ViaGrouping.stPsiPoly_gridPsi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:43:25.108514+00:00
-- url     : https://prove2.me/submissions/ceac8e93-581d-4c26-b2b7-4c2fc40f8217

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Level
import Definitions.Def_Eight_ViaGrouping_LevelCert
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_ViaGrouping_LevelEnd

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (h : StGridPsiPoly) (g : ℕ) (tr : Bool) : StPsiPoly (gridPsi g tr) := h g tr
end Eight.ViaGrouping
