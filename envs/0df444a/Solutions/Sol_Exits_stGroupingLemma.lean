-- Prove2me | solution 1 for Exits.stGroupingLemma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:38:02.148168+00:00
-- url     : https://prove2.me/submissions/99695289-9378-4fd2-b7d9-a9280c0db38d

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
import Theorems.Thm_Exits_stSearchStops
import Theorems.Thm_Eight_ViaGrouping_stSearch
import Theorems.Thm_Eight_ViaGrouping_stTable
import Theorems.Thm_Eight_ViaGrouping_stValue
import Theorems.Thm_Exits_stGroupingLemmaOf
import Theorems.Thm_Value_stValue
import Theorems.Thm_Variance_stSearch


set_option autoImplicit false
section
section
open Exits
open Paper Eight
namespace Exits
theorem _root_.solution : StGroupingLemma := stGroupingLemmaOf stSearchStops Variance.stSearch ViaGrouping.stTable Value.stValue
end Exits
