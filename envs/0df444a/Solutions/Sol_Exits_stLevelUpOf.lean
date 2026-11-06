-- Prove2me | solution 1 for Exits.stLevelUpOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:12:23.71038+00:00
-- url     : https://prove2.me/submissions/ebc33ac2-335d-4fc5-8173-d9c890c14762

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_Eight_ViaGrouping_GridPsi
import Definitions.Def_Eight_SecLevel_EStar
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_ToTuring_Poly_Brute
import Mathlib.Tactic.Ring
import Definitions.Def_Exits_Level
import Theorems.Thm_Eight_ViaGrouping_levelAlgP_gridPsi_correct
import Theorems.Thm_Eight_ViaGrouping_levelAlgP_gridPsi_keeps
import Theorems.Thm_Eight_ViaGrouping_stGridPsi
import Theorems.Thm_Eight_ViaGrouping_stGridPsiPoly


set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Paper Eight Eight.SecNetworks Eight.ViaGrouping
namespace Exits
theorem _root_.solution : StLevelUpOf := by
  intro hL hKp K e E hK h0 hk hc
  have hg : K ≤ 3 * K ^ 8 := by
    have : K ≤ K ^ 8 := Nat.le_self_pow (by norm_num) K
    omega
  -- «Apply Lemma 1 to the network with the smaller total.»
  have h2 := levelAlgP_gridPsi_correct stGridPsi hK hg h0 (hL K e E hK h0 hc)
  have e1 : 3 * K ^ 8 * (3 * K ^ 8) = 9 * K ^ 16 := by ring
  rw [e1] at h2
  exact ⟨levelAlgP_gridPsi_keeps stGridPsiPoly _ (hKp K _ E hk), h2⟩
end Exits
