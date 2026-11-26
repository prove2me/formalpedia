-- Prove2me | solution 1 for CSeparatedNPComplete.dot_const
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:57:31.60583+00:00
-- url     : https://prove2.me/submissions/61e751c1-7bb0-41e7-894b-6a84a92bde77

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (a : Vec n) (r : ℝ) :
    dot a (fun _ => r) = r * dot a 1 := by
  simp only [dot, Pi.one_apply, mul_one, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end CSeparatedNPComplete
