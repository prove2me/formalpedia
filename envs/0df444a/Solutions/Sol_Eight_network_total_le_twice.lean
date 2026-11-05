-- Prove2me | solution 1 for Eight.network_total_le_twice
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:11:00.622716+00:00
-- url     : https://prove2.me/submissions/ca568bd1-30cc-4aa6-a5b0-159b194c2961

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
import Theorems.Thm_Eight_card_tests_le
import Theorems.Thm_Eight_network_total_eq
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
namespace Eight
theorem _root_.solution {g : ℕ} (hg : 0 < g) {Φ : Formula} (h3 : ∀ C ∈ Φ, C.length ≤ 3) (hm : 1 ≤ Φ.length) : (networkOf g Φ).U ≤ 2 * (3 * Φ.length - 1) := by
  rw [network_total_eq hg]
  exact Nat.mul_le_mul_left 2 ((Finset.card_filter_le _ _).trans (card_tests_le hg h3 hm))
end Eight
