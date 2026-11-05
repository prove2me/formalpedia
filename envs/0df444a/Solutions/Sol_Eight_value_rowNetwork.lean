-- Prove2me | solution 1 for Eight.value_rowNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:01:26.281176+00:00
-- url     : https://prove2.me/submissions/74aa6240-ae12-4a13-812d-6cde8f613505

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridDefs
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_Grid
import Theorems.Thm_Eight_rowCut_factors
import Theorems.Thm_Groundwork_Grid_value_rowNet
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
    (rowNetwork W ι).value = Zι W ι :=
  Grid.value_rowNet (fun q => rowCut_factors hlam (hι q)) W _ lam
end Eight
