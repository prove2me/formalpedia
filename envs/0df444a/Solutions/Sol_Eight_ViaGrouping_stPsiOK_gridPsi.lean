-- Prove2me | solution 1 for Eight.ViaGrouping.stPsiOK_gridPsi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:43:23.806934+00:00
-- url     : https://prove2.me/submissions/654e7b38-5a2b-4602-9e51-2db79026055e

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
theorem _root_.solution (h : StGridPsi) (g : ℕ) (tr : Bool) : StPsiOK g tr (gridPsi g tr) := fun lam y Rm hl _ => h g tr lam y Rm hl
end Eight.ViaGrouping
