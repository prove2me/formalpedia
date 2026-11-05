-- Prove2me | solution 1 for ClauseBound.Inst.Rec.sumR_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:11:21.745596+00:00
-- url     : https://prove2.me/submissions/9dd3bd83-7edd-4bb5-8c5b-7411494eb5a9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_RecArith

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec
namespace ClauseBound.Inst.Rec
theorem _root_.solution (w : ℕ) (f : ℕ → ℤ) : sumR w f = ∑ k ∈ range w, f k := by
  rw [sumR, ← List.sum_toFinset _ (List.nodup_range), List.toFinset_range]
end ClauseBound.Inst.Rec
