-- Prove2me | solution 1 for Eight.ViaGrouping.stLemGrouping
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:17:58.594966+00:00
-- url     : https://prove2.me/submissions/14de43a6-70bb-4351-a384-ae50587a9662

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_Eight_ViaGrouping_Keeps
import Definitions.Def_Eight_ViaGrouping_Table
import Definitions.Def_Eight_ViaGrouping_Main
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Theorems.Thm_Eight_ViaGrouping_stLemGrouping_of
import Theorems.Thm_Eight_ViaGrouping_stSearch
import Theorems.Thm_Eight_ViaGrouping_stTable
import Theorems.Thm_Eight_ViaGrouping_stValue


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
namespace Eight.ViaGrouping
theorem _root_.solution : StLemGrouping := stLemGrouping_of stSearch stTable stValue
end Eight.ViaGrouping
