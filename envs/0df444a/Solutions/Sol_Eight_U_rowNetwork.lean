-- Prove2me | solution 1 for Eight.U_rowNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:11:23.312133+00:00
-- url     : https://prove2.me/submissions/94a375a5-497b-4efd-a912-3698f12b2b2f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridDefs
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_Grid
import Theorems.Thm_Groundwork_Grid_U_rowNet
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
    (rowNetwork W ι).U = g ^ 2 * (g - 1) * lam + 2 * ∑ q ∈ rectangles g, crow lam (ι q) :=
  Grid.U_rowNet (Fintype.card_fin g) (Fintype.card_fin g) W _ _
end Eight
