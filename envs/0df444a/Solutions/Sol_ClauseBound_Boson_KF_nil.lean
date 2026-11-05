-- Prove2me | solution 1 for ClauseBound.Boson.KF_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:52:41.844439+00:00
-- url     : https://prove2.me/submissions/1c05bffd-1d0b-4b8a-896e-87b66c33d12d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_ClauseBound_Boson_KF

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
namespace ClauseBound.Boson
theorem _root_.solution (w : ℕ) (r : ℤ) (π σ : Multiset ℕ) : KF [] w r π σ = if w = 0 then op [] r π σ else 0 := by
  simp only [KF, aFam, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, one_mul]
  by_cases h : w = 0
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]
end ClauseBound.Boson
