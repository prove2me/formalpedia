-- Prove2me | solution 1 for Eight.Level.eqMinTotal_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:15:20.582876+00:00
-- url     : https://prove2.me/submissions/83b765f3-f44b-4d14-b6c6-99d0c3be6c6d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_Eight_Level_digOf_le
import Theorems.Thm_P2M_Eight_Level_netOf__row_07c080f825b3
import Theorems.Thm_P2M_Eight_Level_netOf__col_8a246f415134
import Theorems.Thm_Eight_eqMinTotal
import Theorems.Thm_Paper_mem_rectangles


set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}
namespace Eight.Level
theorem _root_.solution (hlam : 1 ≤ lam) (g y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) :
    ((min (netOfι g false lam y Rm).U (netOfι g true lam y Rm).U : ℕ) : ℝ) ≤ rho * ((g : ℝ) ^ 4 * lam) + (g : ℝ) ^ 3 * lam + 2 * (g : ℝ) ^ 4 := by
  rw [netOfι_row, netOfι_col]
  exact eqMinTotal hlam (gridR0 g g lam Rm) (digOf_le g lam y)
end Eight.Level
