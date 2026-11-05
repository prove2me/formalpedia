-- Prove2me | solution 1 for ClauseBound.Boson.Size.abs_bet_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:48:31.710187+00:00
-- url     : https://prove2.me/submissions/7f4f72bf-6c6b-4653-916f-263bf71dcddb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Boson_Defs2
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_ClauseBound_Rec_Window
import Definitions.Def_ClauseBound_Boson_Size
import Theorems.Thm_ClauseBound_Rec_abs_choose_le


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Boson
open Finset
open ClauseBound.Boson.Size
namespace ClauseBound.Boson.Size
theorem _root_.solution {W n : ℕ} (hW : 1 ≤ W) (hn : n ≤ W) {r : ℤ} (h1 : -(W : ℤ) ≤ r) (h2 : r ≤ W) : |bet n r| ≤ 2 ^ (2 * W) := by
  unfold bet
  split_ifs
  · rw [abs_zero]; positivity
  · exact (ClauseBound.Rec.abs_choose_le (r - 1) (n - 1)).trans (pow_le_pow_right₀ (by norm_num) (by omega))
end ClauseBound.Boson.Size
