-- Prove2me | solution 1 for Eight.ViaGrouping.Cost.K2L_le_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:29:43.288276+00:00
-- url     : https://prove2.me/submissions/7a1382c8-e77e-4364-8871-a0b51655de1b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Search
import Definitions.Def_StepMachines_Math_RebalanceArith
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Main
import Theorems.Thm_Eight_SecNetworks_K2L_le


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Cost
namespace Eight.ViaGrouping.Cost
theorem _root_.solution {K : ℕ} (g U P : ℕ) (hK : 1 ≤ K) :
    (K : ℝ) ^ 2 * (Paper.groupedLength K g U P : ℝ) ≤ (K : ℝ) ^ 2 + U + (g : ℝ) * P / K := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have h : (K : ℝ) ^ 3 * (Paper.groupedLength K g U P : ℝ) ≤ (K : ℝ) ^ 3 + K * U + g * P := by exact_mod_cast K2L_le K g U P
  refine le_of_mul_le_mul_right ?_ hKpos
  have e : ((K : ℝ) ^ 2 + U + (g : ℝ) * P / K) * K = (K : ℝ) ^ 3 + K * U + g * P := by field_simp
  rw [e]
  calc (K : ℝ) ^ 2 * (Paper.groupedLength K g U P : ℝ) * K = (K : ℝ) ^ 3 * (Paper.groupedLength K g U P : ℝ) := by ring
    _ ≤ _ := h
end Eight.ViaGrouping.Cost
