-- Prove2me | solution 1 for Eight.ViaGrouping.CLIQUEp_polyTimeSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:08:20.435876+00:00
-- url     : https://prove2.me/submissions/bbba7589-f629-4e0f-b8f2-42f3d7748eec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_Alg
import Theorems.Thm_Eight_ViaGrouping_levelAlgP_gridPsi_keeps
import Theorems.Thm_Eight_ViaGrouping_stGridPsiPoly
import Theorems.Thm_Eight_ViaGrouping_stKeeps
import Theorems.Thm_Eight_stKeeps
import Theorems.Thm_Groundwork_Prog_bruteE_keeps


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (ℓ : ℕ) : (CLIQUEp ℓ).PolyTimeSteps := by
  induction ℓ with
  | zero => exact bruteE_keeps _
  | succ ℓ ih => exact levelAlgP_gridPsi_keeps stGridPsiPoly _ (ViaGrouping.stKeeps (levelK ℓ) _ _ ih)
end Eight.ViaGrouping
