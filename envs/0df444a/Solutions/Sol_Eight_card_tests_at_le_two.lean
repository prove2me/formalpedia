-- Prove2me | solution 1 for Eight.card_tests_at_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:47:33.948357+00:00
-- url     : https://prove2.me/submissions/0cc260d6-e6a3-4395-8558-1c4fed19c3b1

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
import Theorems.Thm_Eight_mem_testsOf
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_SatNet_Consec_pred_unique
import Theorems.Thm_Groundwork_SatNet_Consec_succ_unique
import Theorems.Thm_Groundwork_SatNet_idx_injective
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
variable {Φ : Formula} {g μ k : ℕ}
namespace Eight
theorem _root_.solution (o : Slot g μ k) : #{t ∈ testsOf Φ g μ k | t.1 = o ∨ t.2 = o} ≤ 2 := by
  rw [Finset.filter_or]
  refine (Finset.card_union_le _ _).trans ?_
  have h1 : #{t ∈ testsOf Φ g μ k | t.1 = o} ≤ 1 := by
    refine Finset.card_le_one.2 fun t ht t' ht' => ?_
    obtain ⟨h, e⟩ := Finset.mem_filter.1 ht
    obtain ⟨h', e'⟩ := Finset.mem_filter.1 ht'
    have l := mem_testsOf.1 h
    have l' := mem_testsOf.1 h'
    rw [e] at l
    rw [e'] at l'
    exact Prod.ext (e.trans e'.symm) (l.succ_unique idx_injective l')
  have h2 : #{t ∈ testsOf Φ g μ k | t.2 = o} ≤ 1 := by
    refine Finset.card_le_one.2 fun t ht t' ht' => ?_
    obtain ⟨h, e⟩ := Finset.mem_filter.1 ht
    obtain ⟨h', e'⟩ := Finset.mem_filter.1 ht'
    have l := mem_testsOf.1 h
    have l' := mem_testsOf.1 h'
    rw [e] at l
    rw [e'] at l'
    exact Prod.ext (l.pred_unique idx_injective l') (e.trans e'.symm)
  omega
end Eight
