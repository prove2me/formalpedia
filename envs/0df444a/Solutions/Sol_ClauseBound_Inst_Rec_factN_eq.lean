-- Prove2me | solution 1 for ClauseBound.Inst.Rec.factN_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:41:39.311447+00:00
-- url     : https://prove2.me/submissions/7e541e78-ac70-4326-a8b8-422c023d08aa

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
theorem _root_.solution (k : ℕ) : factN k = k.factorial := by
  rw [factN, prodL_eq]
  have : ∏ i ∈ range k, ((i : ℤ) + 1) = ((k.factorial : ℕ) : ℤ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]; push_cast; rfl
  rw [this, Int.natAbs_natCast]
end ClauseBound.Inst.Rec
