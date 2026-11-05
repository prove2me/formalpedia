-- Prove2me | solution 1 for Eight.neg_one_pow_add_neg_one_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:47:44.322515+00:00
-- url     : https://prove2.me/submissions/ccae9467-0be1-457f-b6e8-41897d223fb3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eight_SecCrossing_Identity

set_option autoImplicit false
section
section
open Eight
open Finset
namespace Eight
theorem _root_.solution {m n : ℕ} (h : Odd (m + n)) : (-1 : ℤ) ^ m + (-1) ^ n = 0 := by
  rcases Nat.even_or_odd m with hm | hm
  · have hn : Odd n := by
      rcases Nat.even_or_odd n with hn | hn
      · exact absurd h (Nat.not_odd_iff_even.2 (hm.add hn))
      · exact hn
    rw [hm.neg_one_pow, hn.neg_one_pow]; norm_num
  · have hn : Even n := by
      rcases Nat.even_or_odd n with hn | hn
      · exact hn
      · exact absurd h (Nat.not_odd_iff_even.2 (hm.add_odd hn))
    rw [hm.neg_one_pow, hn.neg_one_pow]; norm_num
end Eight
