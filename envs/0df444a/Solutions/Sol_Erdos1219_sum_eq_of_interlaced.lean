-- Prove2me | solution 1 for Erdos1219.sum_eq_of_interlaced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:24.580569+00:00
-- url     : https://prove2.me/submissions/f3efc938-643a-4196-94dc-4a1225de2284

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Theorems.Thm_Erdos1219_sum_shift_le

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution (a b : ℕ → Cardinal.{u}) (h1 : ∀ k, a k ≤ b k)
    (h2 : ∀ k, b k ≤ a (k + 1)) : Cardinal.sum a = Cardinal.sum b :=
  le_antisymm (sum_le_sum _ _ h1) ((sum_le_sum _ _ h2).trans (sum_shift_le a))
end Erdos1219
