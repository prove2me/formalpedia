-- Prove2me | solution 1 for Eight.eqMinTotal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:07:27.343417+00:00
-- url     : https://prove2.me/submissions/3240a911-4832-4b85-a863-b725a0dfdbaf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridDefs
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_Grid
import Theorems.Thm_Eight_eqMinTotal_chain
import Theorems.Thm_Groundwork_TM_Run_trans
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
    ((min (rowNetwork W ι).U (colNetwork W ι).U : ℕ) : ℝ) ≤ rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4 :=
  have h := eqMinTotal_chain hlam W hι
  h.1.trans (h.2.1.trans h.2.2)
end Eight
