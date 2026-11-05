-- Prove2me | solution 1 for ClauseBound.Inst.Rec.chooseZ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:20:53.445526+00:00
-- url     : https://prove2.me/submissions/29957906-40e5-4bf3-abf7-ecef72ff7567

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_RecArith
import Theorems.Thm_ClauseBound_Inst_Rec_factN_eq
import Theorems.Thm_ClauseBound_Inst_Rec_fallZ_eq

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec
namespace ClauseBound.Inst.Rec
theorem _root_.solution (a : ℤ) (k : ℕ) : chooseZ a k = Ring.choose a k := by
  have hk : 0 < k.factorial := k.factorial_pos
  have hk' : (0 : ℤ) < (k.factorial : ℤ) := by exact_mod_cast hk
  rw [chooseZ, fallZ_eq, factN_eq, Int.natAbs_mul, Int.natAbs_natCast, Nat.mul_div_cancel_left _ hk]
  rcases lt_or_ge (Ring.choose a k) 0 with h | h
  · rw [if_pos (mul_neg_of_pos_of_neg hk' h)]
    omega
  · rw [if_neg (not_lt.2 (mul_nonneg hk'.le h))]
    omega
end ClauseBound.Inst.Rec
