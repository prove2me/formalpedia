-- Prove2me | solution 1 for CSeparatedNPComplete.is_binary_box_constraints
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:51:17.144842+00:00
-- url     : https://prove2.me/submissions/f95ea5a6-0e28-4771-bf62-6b30462ac809

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} {a : Vec n}
    (ha : is_binary a) : box_constraints a := by
  constructor <;> intro i <;> rcases ha i with h | h <;> simp [h]
end CSeparatedNPComplete
