-- Prove2me | solution 1 for ClauseBound.Boson.Dual.sum_range_eq_list
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:19:17.767548+00:00
-- url     : https://prove2.me/submissions/74e9dad6-b728-4f81-9b80-6918e78b9c45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Scalars
import Definitions.Def_ClauseBound_Boson_Dual

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson ClauseBound.Boson.Dual
open Finset
namespace ClauseBound.Boson.Dual
theorem _root_.solution (F : ℕ → ℤ) (n : ℕ) : ∑ p ∈ range n, F p = ((List.range n).map F).sum := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_range_succ, List.range_succ, List.map_append, List.sum_append, ih]; simp
end ClauseBound.Boson.Dual
