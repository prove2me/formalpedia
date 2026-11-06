-- Prove2me | solution 1 for Eight.ViaGrouping.stGridPsi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:18:12.866201+00:00
-- url     : https://prove2.me/submissions/61f9eeb8-f013-491f-ac53-12ee555d6f96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_GridPsiDefs
import Definitions.Def_Eight_ViaGrouping_LevelDefs
import Definitions.Def_Eight_SecLevel_GridWords
import Definitions.Def_Eight_SecCrossing_Cert
import Definitions.Def_Eight_Level_Presents
import Definitions.Def_Eight_Level_Cert
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Theorems.Thm_Eight_ViaGrouping_gridPsi_eq
import Theorems.Thm_Groundwork_mem_words
attribute [local simp] Groundwork.mem_words



set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution : StGridPsi := fun _ tr _ y Rm hlam _ _ hab _ hz _ hz' => gridPsi_eq hlam tr y Rm hab (mem_words.1 hz) (mem_words.1 hz')
end Eight.ViaGrouping
