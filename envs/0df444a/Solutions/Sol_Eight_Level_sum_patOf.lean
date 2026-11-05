-- Prove2me | solution 1 for Eight.Level.sum_patOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:12:03.249781+00:00
-- url     : https://prove2.me/submissions/4702efe0-c34f-47bc-a8b5-587b469ccc95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecLevel_Grid
import Definitions.Def_Eight_Level_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_SecLevel_GridWords
import Theorems.Thm_ClauseBound_Alg_GridNet_sum_patG
import Theorems.Thm_Groundwork_Grid_nRect_eq
import Theorems.Thm_Paper_mem_rectangles


set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet
open Paper (Rectangle rectangles mem_rectangles FactorsThrough)
variable {g lam : ℕ}
namespace Eight.Level
theorem _root_.solution (g lam : ℕ) (F : (Rectangle g → ℕ) → ℤ) :
    ∑ y ∈ range ((tOf lam + 1) ^ nRect g), F (Eight.Level.patOf g lam y) = ∑ ι ∈ patterns g lam, F ι := by
  rw [nRect_eq]
  exact sum_patG g g (tOf lam) F
end Eight.Level
