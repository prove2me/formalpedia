-- Prove2me | solution 1 for CSeparatedNPComplete.dot_canon_e_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:51:16.597055+00:00
-- url     : https://prove2.me/submissions/d0d2dd5a-1aff-4f65-af1b-9f5ae36f333c

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (a : Vec n) (i : Fin n) :
    dot a (canon_e i.val) = a i := by
  simp only [dot, canon_e, mul_ite, mul_one, mul_zero]
  simp_rw [Fin.val_inj]
  simp
end CSeparatedNPComplete
