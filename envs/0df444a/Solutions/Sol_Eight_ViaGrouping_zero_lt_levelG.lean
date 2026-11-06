-- Prove2me | solution 1 for Eight.ViaGrouping.zero_lt_levelG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:33.34857+00:00
-- url     : https://prove2.me/submissions/6d55bfd8-61fa-4e07-9038-6e63f075f291

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_Alg
import Theorems.Thm_Paper_levelK_ge


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (ℓ : ℕ) : 0 < levelG ℓ := by
  have := levelK_ge ℓ
  unfold levelG
  positivity
end Eight.ViaGrouping
