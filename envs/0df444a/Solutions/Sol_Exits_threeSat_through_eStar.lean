-- Prove2me | solution 1 for Exits.threeSat_through_eStar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:39:03.365696+00:00
-- url     : https://prove2.me/submissions/3e372e59-dd94-4ed0-adb2-1766d75488ce

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Exits_Runs
import Definitions.Def_Exits_Poly
import Definitions.Def_Exits_Grouping
import Definitions.Def_Exits_Level
import Definitions.Def_Exits_Count
import Definitions.Def_Exits_Decides
import Definitions.Def_Variance_Grouping
import Definitions.Def_Value_End
import Definitions.Def_Enumerate_Enumeration
import Definitions.Def_Enumerate_Named
import Definitions.Def_Suffices_Main
import Definitions.Def_Eight_ViaGrouping_Table
import Definitions.Def_Exits_End
import Theorems.Thm_Exits_eStar_eq_zero
import Theorems.Thm_Exits_stProofNamed
import Theorems.Thm_Enumerate_stEnumeration
import Theorems.Thm_Exits_stThroughEStarOf


set_option autoImplicit false
section
section
open Exits
open Paper Eight
namespace Exits
theorem _root_.solution : Sat3.ThmEveryDelta := stThroughEStarOf eStar_eq_zero Enumerate.stEnumeration stProofNamed
end Exits
