-- Prove2me | solution 1 for Exits.stProofNamedOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:16:44.714835+00:00
-- url     : https://prove2.me/submissions/b53605bc-a7c1-48dc-978f-36dae5050c69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Exits_AlgDefs
import Definitions.Def_Eight_ViaGrouping_Count
import Definitions.Def_Eight_SecLevel_EStar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_Exits_Decides
import Theorems.Thm_Exits_decidesSparse_of
import Theorems.Thm_Eight_ViaGrouping_count_cost_pos_of
import Theorems.Thm_Eight_ViaGrouping_count_isPolyT
import Theorems.Thm_Eight_two_le_of_le
import Theorems.Thm_P2M_Eight_delta__le_fd4e6e087c27


set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping Suffices Enumerate
namespace Exits
theorem _root_.solution : StProofNamedOf := by
  intro hS hL hKp δ M τ K E hδ hδ1 hM hEn hK hEk hE
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have hδ' : 0 < δ / (3 * (M : ℝ)) := by positivity
  have h3 := delta'_le hδ1 hMR
  have hK2 := two_le_of_le hδ' h3 hK
  -- Lemma 1 for (K, δ'/12), and the paragraph «Cost»
  obtain ⟨A, hA⟩ := ViaGrouping.count_cost_pos_of hδ' (by linarith) (by positivity) hK (hL K _ E hK2 (by positivity) hE)
  obtain ⟨s1, s2⟩ := hS δ M τ hδ hM hEn
  exact ⟨s1 _ (count_isPolyT (hKp K _ E hEk) _ 3), s2 _ A (decidesSparse_of hA)⟩
end Exits
