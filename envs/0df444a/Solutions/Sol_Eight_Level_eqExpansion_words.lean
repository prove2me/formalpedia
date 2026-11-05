-- Prove2me | solution 1 for Eight.Level.eqExpansion_words
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:08:44.419136+00:00
-- url     : https://prove2.me/submissions/59d86c4d-7422-47a1-87c2-5c91d372168b

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_Eight_Level_card_rectangles_eq
import Theorems.Thm_Eight_Level_sum_patOf
import Theorems.Thm_Eight_eqExpansion
import Theorems.Thm_Groundwork_Grid_ZW_eq_Z
import Theorems.Thm_Groundwork_Grid_sum_patOf
import Theorems.Thm_Paper_mem_rectangles


set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}
namespace Eight.Level
theorem _root_.solution (hlam : 1 ≤ lam) (Rm : Inst (Fin (g * g)) (List Bool)) :
    2 ^ (tOf lam * nRect g) * Inst.ZW lam [] Rm = ∑ y ∈ range ((tOf lam + 1) ^ nRect g), Zι (gridR0 g g lam Rm) (Eight.Level.patOf g lam y) := by
  rw [sum_patOf g lam fun ι => Zι (gridR0 g g lam Rm) ι, ZW_eq_Z lam Rm fun _ => false, ← card_rectangles_eq]
  exact eqExpansion hlam (instW lam Rm) (fun _ => false) finProdFinEquiv.symm
end Eight.Level
