-- Prove2me | solution 1 for ClauseBound.Inst.Rec.fallZ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:08:45.012162+00:00
-- url     : https://prove2.me/submissions/62f891d8-95f1-4f04-bd8c-dee98b928dda

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_RecArith
import Theorems.Thm_PaddedDescent_F_prodL_eq


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec
namespace ClauseBound.Inst.Rec
theorem _root_.solution (a : ℤ) (k : ℕ) : fallZ a k = k.factorial * Ring.choose a k := by
  rw [fallZ, prodL_eq, ← descPochhammer_eval_eq_prod_range, ← nsmul_eq_mul, ← Ring.descPochhammer_eq_factorial_smul_choose,
    Polynomial.eval_eq_smeval]
end ClauseBound.Inst.Rec
