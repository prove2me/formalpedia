-- Prove2me | solution 1 for Eight.ViaGrouping.NETWORKp_keeps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:17:35.869684+00:00
-- url     : https://prove2.me/submissions/51db8dfa-496c-4da8-b133-c8e4bfaf2962

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_Alg
import Theorems.Thm_Eight_ViaGrouping_CLIQUEp_polyTimeSteps
import Theorems.Thm_Eight_ViaGrouping_stKeeps
import Theorems.Thm_Eight_stKeeps


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (ℓ : ℕ) : AlgKeeps (NETWORKp ℓ) := ViaGrouping.stKeeps (levelK ℓ) (levelG ℓ) _ (CLIQUEp_polyTimeSteps ℓ)
end Eight.ViaGrouping
