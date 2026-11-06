-- Prove2me | solution 1 for Eight.ViaGrouping.levelAlgP_gridPsi_keeps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:01:44.369707+00:00
-- url     : https://prove2.me/submissions/639c2222-5d76-45a0-b581-3c8899a74084

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Level
import Definitions.Def_Eight_ViaGrouping_LevelCert
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Theorems.Thm_Eight_ViaGrouping_stLevelKeepsP
import Theorems.Thm_Eight_ViaGrouping_stPsiPoly_gridPsi

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (h : StGridPsiPoly) (g : ℕ) {NA : NetAlg} (hN : AlgKeeps NA) : (levelAlgP g (gridPsi g false) (gridPsi g true) NA).Keeps :=
  stLevelKeepsP g _ _ NA (stPsiPoly_gridPsi h g false) (stPsiPoly_gridPsi h g true) hN
end Eight.ViaGrouping
