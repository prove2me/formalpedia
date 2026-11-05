-- Prove2me | solution 1 for Eight.eqMinTotal_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:00:35.60902+00:00
-- url     : https://prove2.me/submissions/d8054a0d-615c-443d-8947-cad38431c3cf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridDefs
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_Grid
import Theorems.Thm_Eight_U_rowNetwork
import Theorems.Thm_Eight_U_colNetwork
import Theorems.Thm_Eight_c_sum
import Theorems.Thm_Eight_lemPieces
import Theorems.Thm_Paper_card_rectangles
import Theorems.Thm_Paper_card_rectangles_le
import Theorems.Thm_Paper_mem_rectangles


set_option autoImplicit false
section
section
open Eight
open Finset Groundwork
open Paper (Rectangle rectangles mem_rectangles card_rectangles card_rectangles_le Settings RowSetting FactorsThrough)
variable {g lam : ℕ}
namespace Eight
theorem _root_.solution (hlam : 1 ≤ lam) (W : Inst (Fin g × Fin g) (Bits lam)) {ι : Rectangle g → ℕ} (hι : ∀ q, ι q ≤ tOf lam) :
    ((min (rowNetwork W ι).U (colNetwork W ι).U : ℕ) : ℝ) ≤ (((rowNetwork W ι).U : ℝ) + (colNetwork W ι).U) / 2 ∧
      (((rowNetwork W ι).U : ℝ) + (colNetwork W ι).U) / 2 ≤ (g : ℝ) ^ 3 * lam + #(rectangles g) * (11 * (lam : ℝ) / 3 + 8) ∧
      (g : ℝ) ^ 3 * lam + #(rectangles g) * (11 * (lam : ℝ) / 3 + 8) ≤ rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4 := by
  refine ⟨?_, ?_, ?_⟩
  · have h : 2 * min (rowNetwork W ι).U (colNetwork W ι).U ≤ (rowNetwork W ι).U + (colNetwork W ι).U := by omega
    have h' : 2 * ((min (rowNetwork W ι).U (colNetwork W ι).U : ℕ) : ℝ) ≤ ((rowNetwork W ι).U : ℝ) + (colNetwork W ι).U := by exact_mod_cast h
    linarith
  · have h0 : g ^ 2 * (g - 1) * lam ≤ g ^ 3 * lam :=
      Nat.mul_le_mul_right _ (by
        calc g ^ 2 * (g - 1) ≤ g ^ 2 * g := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
          _ = g ^ 3 := by ring)
    have h1 : (rowNetwork W ι).U + (colNetwork W ι).U ≤ 2 * (g ^ 3 * lam) + 2 * ∑ q ∈ rectangles g, (crow lam (ι q) + ccol lam (ι q)) := by
      rw [U_rowNetwork, U_colNetwork, Finset.sum_add_distrib]
      omega
    have h1' : ((rowNetwork W ι).U : ℝ) + (colNetwork W ι).U ≤
        2 * ((g : ℝ) ^ 3 * lam) + 2 * ∑ q ∈ rectangles g, ((crow lam (ι q) + ccol lam (ι q) : ℕ) : ℝ) := by exact_mod_cast h1
    have h2 : ∑ q ∈ rectangles g, ((crow lam (ι q) + ccol lam (ι q) : ℕ) : ℝ) ≤ #(rectangles g) * (11 * (lam : ℝ) / 3 + 8) := by
      -- «By Lemma 2(c), c^row_i + c^col_i ≤ 11λ/3 + 8»
      rw [← nsmul_eq_mul]
      refine Finset.sum_le_card_nsmul _ _ _ fun q _ => (lemPieces.c_sum lam _ hlam (hι q)).trans_eq ?_
      unfold rho
      ring
    linarith
  · have h5 := card_rectangles_le g
    have hpos : (0 : ℝ) ≤ 11 * (lam : ℝ) / 3 + 8 := by positivity
    have h6 := mul_le_mul_of_nonneg_right h5 hpos
    unfold rho
    linarith
end Eight
