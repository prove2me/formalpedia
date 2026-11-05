-- Prove2me | solution 1 for ClauseBound.Grid.two_mul_pairs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:34:21.963865+00:00
-- url     : https://prove2.me/submissions/4154fd0f-da5c-4c81-988c-57318a47906f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
import Theorems.Thm_Groundwork_card_pairs


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
namespace ClauseBound.Grid
theorem _root_.solution (X : Type) [Fintype X] [LinearOrder X] :
    2 * #(pairs X) = Fintype.card X * (Fintype.card X - 1) := by
  rw [card_pairs, Nat.choose_two_right, Nat.mul_div_cancel' (even_iff_two_dvd.1 (Nat.even_mul_pred_self _))]
end ClauseBound.Grid
