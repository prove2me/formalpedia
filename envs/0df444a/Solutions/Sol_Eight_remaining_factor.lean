-- Prove2me | solution 1 for Eight.remaining_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:54:00.275071+00:00
-- url     : https://prove2.me/submissions/ce239702-081a-4b1e-81ef-846feca78e08

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
import Theorems.Thm_Eight_remaining_factor_query
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight
open Finset Groundwork Groundwork.Prog Groundwork.SatNet Paper
namespace Eight
theorem _root_.solution (C₁ g : ℕ) {δ' : ℝ} (hδ' : 0 < δ') : ∃ A : ℕ, ∀ m : ℕ,
    (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) ^ C₁ ≤ A * (2 : ℝ) ^ (δ' * m / 4) := by
  obtain ⟨A, hA⟩ := remaining_factor_query C₁ 1 g hδ'
  refine ⟨A, fun m => le_trans ?_ (hA m)⟩
  have h0 : (0 : ℝ) ≤ (C₁ : ℝ) * (2 : ℝ) ^ (δ' * g) * ((6 * ((m + g - 1) / g) + 1 : ℕ) : ℝ) ^ C₁ := by positivity
  have h1 : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) * ((m : ℝ) + 1) ^ 1 := by
    have : (0 : ℝ) ≤ m := by positivity
    push_cast
    linarith
  exact le_mul_of_one_le_right h0 h1
end Eight
