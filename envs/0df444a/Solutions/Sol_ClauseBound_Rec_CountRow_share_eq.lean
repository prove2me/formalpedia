-- Prove2me | solution 1 for ClauseBound.Rec.CountRow.share_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:50:04.709454+00:00
-- url     : https://prove2.me/submissions/520bb124-7cd6-4c02-bbcc-3ccaa675bb56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
import Theorems.Thm_ClauseBound_Rec_CountRow_two_mul_card_odd_add
import Theorems.Thm_ClauseBound_Rec_card_BLab
import Theorems.Thm_ClauseBound_Rec_card_blk_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {n h : ℕ}
namespace ClauseBound.Rec.CountRow
theorem _root_.solution (hh : 1 ≤ h) (b : Fin (nblk n h)) :
    (#(oddSet n h b) : ℝ) / Fintype.card (BLab n h b)
      = (((2 ^ #(blk n h b.val) - 1) * 2 ^ (h - #(blk n h b.val)) : ℕ) : ℝ) / ((2 ^ (h + 1) : ℕ) : ℝ) := by
  have e0 : Fintype.card {k : Fin n // k.val / h = b.val} = #(blk n h b.val) := Fintype.card_subtype _
  have e1 : 2 * #(oddSet n h b) + 2 ^ #(blk n h b.val) = Fintype.card (BLab n h b) := by
    rw [← e0]
    exact two_mul_card_odd_add _
  have e3 : #(blk n h b.val) ≤ h := card_blk_le hh _
  rw [card_BLab b] at e1
  rw [card_BLab b]
  generalize #(blk n h b.val) = N at e1 e3
  generalize #(oddSet n h b) = s at e1
  have c1 : ((2 ^ N - 1 : ℕ) : ℝ) = 2 ^ N - 1 := by
    rw [Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    ring
  have c2 : (2 : ℝ) ^ (h + 1) = 2 * (2 ^ (h - N) * 2 ^ N) := by
    rw [← pow_add, Nat.sub_add_cancel e3, pow_succ]
    ring
  have c3 : (4 : ℝ) ^ N = (2 ^ N) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  have e1' : 2 * (s : ℝ) + 2 ^ N = (2 ^ N) ^ 2 := by
    rw [← c3]
    exact_mod_cast e1
  rw [Nat.cast_mul, c1]
  push_cast
  rw [c2, c3]
  have ha : (0 : ℝ) < 2 ^ N := by positivity
  have hc : (0 : ℝ) < 2 ^ (h - N) := by positivity
  generalize (2 : ℝ) ^ N = a at e1' ha
  generalize (2 : ℝ) ^ (h - N) = c at hc
  have hs : (s : ℝ) = (a ^ 2 - a) / 2 := by linarith
  rw [hs, div_eq_div_iff (by positivity) (by positivity)]
  ring
end ClauseBound.Rec.CountRow
