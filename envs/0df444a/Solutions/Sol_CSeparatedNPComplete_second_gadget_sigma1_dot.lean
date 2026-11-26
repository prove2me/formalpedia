-- Prove2me | solution 1 for CSeparatedNPComplete.second_gadget_sigma1_dot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:43.800696+00:00
-- url     : https://prove2.me/submissions/c791b533-eb19-45b0-96f0-a579b0c4be6d

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
theorem _root_.solution {n : ℕ} (m : ℝ) (a : Vec n) :
    dot a (second_gadget_sigma1 m) =
      second_gadget_gamma n m * second_gadget_gamma n m * dot a 1 := by
  simp only [dot, second_gadget_sigma1, Pi.one_apply, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring
end CSeparatedNPComplete
