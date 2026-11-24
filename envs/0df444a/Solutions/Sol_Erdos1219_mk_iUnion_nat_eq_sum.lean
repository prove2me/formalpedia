-- Prove2me | solution 1 for Erdos1219.mk_iUnion_nat_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:27.799801+00:00
-- url     : https://prove2.me/submissions/608e87e4-4566-4e88-a881-7b54a5b2bcb7

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
namespace Erdos1219
theorem _root_.solution {V : Type u} (t : ℕ → Set V) (h : Pairwise (Disjoint on t)) :
    #(⋃ p, t p) = Cardinal.sum fun p => #(t p) := by
  have := mk_iUnion_eq_sum_mk_lift h
  simpa using this
end Erdos1219
