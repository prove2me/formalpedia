-- Prove2me | solution 1 for Eight.rowCut_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:54:30.779188+00:00
-- url     : https://prove2.me/submissions/8b09569a-a13b-45f5-b924-7334776416ea

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
theorem _root_.solution (hlam : 1 ≤ lam) {i : ℕ} (hi : i ≤ tOf lam) : (rowCut lam i).Factors (Eight.A lam i) := fun x y u v =>
  ((stFact lam hlam i hi).1 x y u v).trans
    (SingleBitPieces.Level.Pieces.sum_ofFn _ fun θ => fTop (false, i, List.ofFn x, List.ofFn y, θ) * fBot (false, i, List.ofFn u, List.ofFn v, θ))
end Eight
