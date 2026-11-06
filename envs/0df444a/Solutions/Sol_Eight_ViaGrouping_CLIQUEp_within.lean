-- Prove2me | solution 1 for Eight.ViaGrouping.CLIQUEp_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:25:04.167255+00:00
-- url     : https://prove2.me/submissions/d291f61e-5f35-41bf-8298-be9eb4dcf448

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LemGrouping
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_ViaGrouping_Alg
import Theorems.Thm_Eight_ViaGrouping_two_le_levelK
import Theorems.Thm_Eight_Level_levelE_nonneg
import Theorems.Thm_Eight_ViaGrouping_levelAlgP_gridPsi_correct
import Theorems.Thm_Eight_ViaGrouping_stGridPsi
import Theorems.Thm_Eight_ViaGrouping_stLemGrouping
import Theorems.Thm_Groundwork_Prog_bruteE_correct
import Theorems.Thm_Paper_levelK_succ


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Paper Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (ℓ : ℕ) : (CLIQUEp ℓ).Within (levelK ℓ) (Level.levelE ℓ) := by
  induction ℓ with
  | zero => exact bruteE_correct _
  | succ ℓ ih =>
    have hK : 2 ≤ levelK ℓ := two_le_levelK ℓ
    have hg : levelK ℓ ≤ levelG ℓ := by
      have : levelK ℓ ≤ levelK ℓ ^ 8 := Nat.le_self_pow (by norm_num) _
      unfold levelG
      omega
    have h := levelAlgP_gridPsi_correct stGridPsi hK hg (Level.levelE_nonneg ℓ) (stLemGrouping (levelK ℓ) (Level.levelE ℓ) (CLIQUEp ℓ) hK (Level.levelE_nonneg ℓ) ih)
    rw [levelK_succ]
    exact h
end Eight.ViaGrouping
