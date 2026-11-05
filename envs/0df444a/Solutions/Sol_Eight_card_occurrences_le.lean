-- Prove2me | solution 1 for Eight.card_occurrences_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:50:45.601577+00:00
-- url     : https://prove2.me/submissions/7cc810ba-12e6-4bce-a204-c58102e3cfd4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecProof_NetworkDefs
import Definitions.Def_SingleBitPieces_SecProof_Cost
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Mathlib.Tactic
import Definitions.Def_Eight_SecProof_Network
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_SatNet_card_used_le
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
namespace Eight
theorem _root_.solution (g : ℕ) (Φ : Formula) : #(occurrences g Φ) ≤ 3 * Φ.length := by
  have h := card_used_le (φ := Φ) (g := g) (μ := clusterSize g Φ) (k := 3)
  have e : occurrences g Φ = ({p : Slot g (clusterSize g Φ) 3 | lit Φ p ≠ none} : Finset _) := rfl
  rw [e]
  omega
end Eight
