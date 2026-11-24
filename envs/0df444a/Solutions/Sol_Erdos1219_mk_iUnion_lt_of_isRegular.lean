-- Prove2me | solution 1 for Erdos1219.mk_iUnion_lt_of_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:40:23.24072+00:00
-- url     : https://prove2.me/submissions/f93f30e4-53dd-4456-8d08-fde05afc87d6

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution {V ι : Type u} {c : Cardinal.{u}} (hc : c.IsRegular)
    (hι : #ι < c) (t : ι → Set V) (ht : ∀ i, #(t i) < c) : #(⋃ i, t i) < c :=
  mk_iUnion_le_sum_mk.trans_lt (sum_lt_of_isRegular hc hι ht)
end Erdos1219
