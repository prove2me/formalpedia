-- Prove2me | solution 1 for ClauseBound.Boson.Size.card_toFinset_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:49:13.43934+00:00
-- url     : https://prove2.me/submissions/a487c829-4972-48ae-8957-870c28bb7704

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Rec_Window
import Definitions.Def_ClauseBound_Boson_Size
import Theorems.Thm_ClauseBound_Boson_Size_le_sum_of_mem

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Size
namespace ClauseBound.Boson.Size
theorem _root_.solution {π : Multiset ℕ} {W : ℕ} (h : π.sum ≤ W) : #π.toFinset ≤ W + 1 := by
  rw [← card_range (W + 1)]
  exact card_le_card fun l hl => mem_range.2 (Nat.lt_succ_of_le ((le_sum_of_mem (Multiset.mem_toFinset.1 hl)).trans h))
end ClauseBound.Boson.Size
