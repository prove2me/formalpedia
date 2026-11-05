-- Prove2me | solution 1 for ClauseBound.Inst.Rec.nblk_le_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:09:50.013069+00:00
-- url     : https://prove2.me/submissions/d2c1c4a2-fd9a-4484-adfc-26bf634cba81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_RecArith
import Theorems.Thm_ClauseBound_Rec_nblk_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec
namespace ClauseBound.Inst.Rec
theorem _root_.solution (lam h : ℕ) : Pieces.nblk lam h ≤ lam := by
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · rw [Pieces.nblk, Nat.div_zero]; exact Nat.zero_le _
  · exact nblk_le lam hh
end ClauseBound.Inst.Rec
