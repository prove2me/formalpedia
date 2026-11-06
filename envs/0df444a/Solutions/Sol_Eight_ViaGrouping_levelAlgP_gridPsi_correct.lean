-- Prove2me | solution 1 for Eight.ViaGrouping.levelAlgP_gridPsi_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:17:29.023802+00:00
-- url     : https://prove2.me/submissions/a1f4a7d8-27b4-4c60-b43e-d9a52b5c68b3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Level
import Definitions.Def_Eight_ViaGrouping_LevelCert
import Definitions.Def_Eight_ViaGrouping_Bridge
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Theorems.Thm_Eight_ViaGrouping_stLevelP
import Theorems.Thm_Eight_ViaGrouping_stPsiOK_gridPsi

set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Eight.SecNetworks Eight.Level
namespace Eight.ViaGrouping
theorem _root_.solution (h : StGridPsi) {K g : ℕ} {e : ℝ} {NA : NetAlg} (hK : 2 ≤ K) (hg : K ≤ g) (h0 : 0 ≤ e) (hN : Correct NA g K e (e + 2)) :
    (levelAlgP g (gridPsi g false) (gridPsi g true) NA).Correct (g * g) ((rho + 2 / K) * e + 2 / K) :=
  stLevelP K g e _ _ NA hK hg h0 (stPsiOK_gridPsi h g false) (stPsiOK_gridPsi h g true) hN
end Eight.ViaGrouping
