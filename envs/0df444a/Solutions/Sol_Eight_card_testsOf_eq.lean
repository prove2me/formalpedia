-- Prove2me | solution 1 for Eight.card_testsOf_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:48:19.26819+00:00
-- url     : https://prove2.me/submissions/388a33e5-1300-40dc-bfd5-612847098a7b

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
import Theorems.Thm_Eight_mem_occurrencesOf
import Theorems.Thm_Eight_mem_testsOf
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_SatNet_Consec_pred_unique
import Theorems.Thm_Groundwork_SatNet_Link_used_right
import Theorems.Thm_Groundwork_SatNet_idx_injective
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
variable {Φ : Formula} {g μ k : ℕ}
namespace Eight
theorem _root_.solution : #(testsOf Φ g μ k) = #{q ∈ occurrencesOf Φ g μ k | ∃ p, Link Φ p q} := by
  refine Finset.card_bij (fun t _ => t.2) ?_ ?_ ?_
  · intro t ht
    have l := mem_testsOf.1 ht
    exact Finset.mem_filter.2 ⟨mem_occurrencesOf.2 l.used_right, t.1, l⟩
  · intro t ht t' ht' e
    have l := mem_testsOf.1 ht
    have l' := mem_testsOf.1 ht'
    have e : t.2 = t'.2 := e
    rw [e] at l
    exact Prod.ext (l.pred_unique idx_injective l') e
  · intro q hq
    obtain ⟨p, l⟩ := (Finset.mem_filter.1 hq).2
    exact ⟨(p, q), mem_testsOf.2 l, rfl⟩
end Eight
