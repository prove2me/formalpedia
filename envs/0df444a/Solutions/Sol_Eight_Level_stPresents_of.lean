-- Prove2me | solution 1 for Eight.Level.stPresents_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:47:33.148789+00:00
-- url     : https://prove2.me/submissions/ccc0ae17-1f4b-4288-8c41-0fe1338b1609

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_Defs
import Definitions.Def_SingleBitPieces_Level_Presents
import Mathlib.Tactic
import Definitions.Def_Eight_Level_Presents
import Theorems.Thm_Eight_Level_Presents_tOf_le
import Theorems.Thm_Eight_Level_Presents_presentsP8
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open Eight Eight.Level
open Finset Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Stepped SingleBitPieces.Level.Presents
open Presents
namespace Eight.Level
theorem _root_.solution (hP : StPieces) : StPresents := fun g tr =>
  ⟨sideA g, fun _ _ lam R c B t S Rm y hl ht hy hR =>
    presentsP8 eightF rfl (fun ℓ => (tOf_le ℓ).trans (Nat.le_mul_of_pos_left ℓ (by norm_num))) g tr lam R c B t S Rm y (hP (lam c) hl).2 hl ht
      (hy.trans_le (Nat.pow_le_pow_left (Nat.succ_le_succ (tOf_le (lam c))) _)) hR⟩
end Eight.Level
