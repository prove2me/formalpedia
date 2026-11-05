-- Prove2me | solution 1 for Exits.stAlgorithmOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:44:06.492301+00:00
-- url     : https://prove2.me/submissions/34cf2ce6-2b4d-4595-8e81-c207ae5f8fad

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
import Theorems.Thm_Eight_Level_firstLevel_spec
import Theorems.Thm_Eight_numSat_pos_iff
import Theorems.Thm_P2M_Eight_delta__le_fd4e6e087c27


set_option autoImplicit false
section
section
open Exits
open Groundwork Groundwork.Prog Groundwork.Stepped Paper Eight Eight.SecNetworks Eight.ViaGrouping Suffices Enumerate
namespace Exits
theorem _root_.solution : StAlgorithmOf := by
  intro hS hC δ M τ hδ' hδ hδ1 hM hEn
  have hMR : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  obtain ⟨hK, hE⟩ := Level.firstLevel_spec hδ'
  have h3 := delta'_le hδ1 hMR
  obtain ⟨hp, A, hA⟩ := hC (δ / (3 * (M : ℝ))) (Level.firstLevel hδ') hδ' (by linarith) hK hE
  obtain ⟨s1, s2⟩ := hS δ M τ hδ hM hEn
  refine ⟨s1 _ hp, s2 _ A (decidesSparse_of fun Φ hΦ => ?_)⟩
  obtain ⟨T, hrun, hT⟩ := hA Φ hΦ
  exact ⟨T, _, hrun, by rw [Nat.cast_pos]; exact numSat_pos_iff Φ, hT⟩
end Exits
