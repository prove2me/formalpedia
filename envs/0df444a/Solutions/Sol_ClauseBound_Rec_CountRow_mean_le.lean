-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.mean_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:52:51.568748+00:00
-- url     : https://prove2.me/submissions/5aa88be8-f84c-4361-83bb-e37ee9d5a2da

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_CountRow_two_mul_card_odd_le

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {n h : ℕ}
namespace ClauseBound.Rec.CountRow
theorem _root_.solution (n h : ℕ) : mean n h ≤ (nblk n h : ℝ) / 2 := by
  have h1 (b : Fin (nblk n h)) : (#(oddSet n h b) : ℝ) / Fintype.card (BLab n h b) ≤ 1 / 2 := by
    have h2 : 2 * #(oddSet n h b) ≤ Fintype.card (BLab n h b) := two_mul_card_odd_le _
    have h3 : (2 : ℝ) * #(oddSet n h b) ≤ Fintype.card (BLab n h b) := by exact_mod_cast h2
    have hc : (0 : ℝ) < Fintype.card (BLab n h b) := by exact_mod_cast Fintype.card_pos
    rw [div_le_div_iff₀ hc (by norm_num)]
    linarith
  calc mean n h ≤ ∑ _b : Fin (nblk n h), (1 / 2 : ℝ) := Finset.sum_le_sum fun b _ => h1 b
    _ = (nblk n h : ℝ) / 2 := by simp; ring
end ClauseBound.Rec.CountRow
