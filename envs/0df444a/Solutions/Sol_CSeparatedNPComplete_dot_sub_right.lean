-- Prove2me | solution 1 for CSeparatedNPComplete.dot_sub_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:57:51.028671+00:00
-- url     : https://prove2.me/submissions/29bac8af-e204-4671-89d9-8a25bd6e3915

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (a u v : Vec n) :
    dot a (u - v) = dot a u - dot a v := by
  simp [dot, mul_sub, Finset.sum_sub_distrib]
end CSeparatedNPComplete
