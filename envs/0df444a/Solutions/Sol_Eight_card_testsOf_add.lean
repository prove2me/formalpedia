-- Prove2me | solution 1 for Eight.card_testsOf_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:56:56.38903+00:00
-- url     : https://prove2.me/submissions/92376cb7-a00a-4681-a98f-f0b2f3e9dea0

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
import Theorems.Thm_Eight_card_testsOf_eq
import Theorems.Thm_Eight_card_first_eq
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
variable {Φ : Formula} {g μ k : ℕ}
namespace Eight
theorem _root_.solution (hk : ∀ C ∈ Φ, C.length ≤ k) (hm : Φ.length ≤ g * μ) : #(testsOf Φ g μ k) + #(occurring Φ) = #(occurrencesOf Φ g μ k) := by
  rw [card_testsOf_eq, ← card_first_eq hk hm]
  exact Finset.card_filter_add_card_filter_not _
end Eight
