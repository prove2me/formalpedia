-- Prove2me | solution 1 for Eight.U_colNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:11:32.106105+00:00
-- url     : https://prove2.me/submissions/57bdff19-7b1e-43c8-aa1b-8db29b2c54aa

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridDefs
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_Grid
import Theorems.Thm_Groundwork_Grid_U_rowNet
import Theorems.Thm_P2M_Groundwork_Grid_sum___swap_e6d8d32443c0
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
theorem _root_.solution (W : Inst (Fin g × Fin g) (Bits lam)) (ι : Rectangle g → ℕ) :
    (colNetwork W ι).U = g ^ 2 * (g - 1) * lam + 2 * ∑ q ∈ rectangles g, ccol lam (ι q) := by
  rw [rectangles, ← Grid.sum_Ω_swap fun q => ccol lam (ι q)]
  exact Grid.U_rowNet (Fintype.card_fin g) (Fintype.card_fin g) _ _ _
end Eight
