-- Prove2me | solution 1 for Eight.colCut_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:31.807985+00:00
-- url     : https://prove2.me/submissions/444ee05a-8471-4b7f-964a-f9f4f7051db9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_GridDefs
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_SingleBitPieces_Level_Pieces
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_Grid
import Theorems.Thm_Eight_Fact_sum_ofFn
import Theorems.Thm_Eight_stFact
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Paper_card_rectangles
import Theorems.Thm_Paper_card_rectangles_le
import Theorems.Thm_Paper_mem_rectangles
import Theorems.Thm_SingleBitPieces_Level_Pieces_sum_ofFn


set_option autoImplicit false
section
section
open Eight
open Finset Groundwork
open Paper (Rectangle rectangles mem_rectangles card_rectangles card_rectangles_le Settings RowSetting FactorsThrough)
variable {g lam : ℕ}
namespace Eight
theorem _root_.solution (hlam : 1 ≤ lam) {i : ℕ} (hi : i ≤ tOf lam) : (colCut lam i).Factors fun x u y v => Eight.A lam i x y u v := fun x u y v =>
  ((stFact lam hlam i hi).2.1 x y u v).trans
    (SingleBitPieces.Level.Pieces.sum_ofFn _ fun θ => fTop (true, i, List.ofFn x, List.ofFn u, θ) * fBot (true, i, List.ofFn y, List.ofFn v, θ))
end Eight
