-- Prove2me | solution 1 for Eight.card_tests_back_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:49:30.444122+00:00
-- url     : https://prove2.me/submissions/8ae2cf62-b0df-49f2-b114-f207e8e7b065

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
import Theorems.Thm_Groundwork_SatNet_Link_fst_le
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
variable {Φ : Formula} {g μ k : ℕ}
namespace Eight
theorem _root_.solution {a b : Fin g} (h : a < b) : #{t ∈ testsOf Φ g μ k | t.1.1 = b ∧ t.2.1 = a} = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro t ht ⟨e1, e2⟩
  have := (mem_testsOf.1 ht).fst_le
  rw [e1, e2] at this
  exact absurd h (not_lt.2 this)
end Eight
