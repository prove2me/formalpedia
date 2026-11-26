-- Prove2me | solution 1 for CSeparatedNPComplete.second_gadget_sigma3_dot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:48.885281+00:00
-- url     : https://prove2.me/submissions/6588a803-102a-44ee-b6c3-2644b9fa6dd9

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Definitions.Def_CSeparatedNPComplete_Gadget

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : ℕ} (m : ℝ) (a s : Vec n) :
    dot a (second_gadget_sigma3 m s) =
      second_gadget_gamma n m * second_gadget_gamma n m * m * dot a s := by
  simp only [dot, second_gadget_sigma3]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring
end CSeparatedNPComplete
