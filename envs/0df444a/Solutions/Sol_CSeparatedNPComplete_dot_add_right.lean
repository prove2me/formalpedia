-- Prove2me | solution 1 for CSeparatedNPComplete.dot_add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:57:46.721147+00:00
-- url     : https://prove2.me/submissions/483f21f5-afd1-492f-bc46-98ac87cb7a92

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
    dot a (u + v) = dot a u + dot a v := by
  simp [dot, mul_add, Finset.sum_add_distrib]
end CSeparatedNPComplete
