-- Prove2me | solution 1 for Eight.ViaGrouping.COUNTp_polyTimeSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:24:21.43698+00:00
-- url     : https://prove2.me/submissions/cc814233-176d-4807-8c60-1b1b28bc09ff

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_Alg
import Theorems.Thm_Eight_ViaGrouping_NETWORKp_keeps
import Theorems.Thm_Eight_ViaGrouping_satProcs_keepsP


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (ℓ : ℕ) : PolyTimeSteps (COUNTp ℓ) := NETWORKp_keeps ℓ Formula _ (satProcs_keepsP _ _)
end Eight.ViaGrouping
