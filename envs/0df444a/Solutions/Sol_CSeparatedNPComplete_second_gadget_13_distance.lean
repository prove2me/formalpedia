-- Prove2me | solution 1 for CSeparatedNPComplete.second_gadget_13_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:10.629994+00:00
-- url     : https://prove2.me/submissions/e8fabcf2-cccc-4d31-82f0-4ad30860e4e8

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
theorem _root_.solution {n : ℕ} (m c : ℝ) (a : Vec n) :
    dot a (sqVec (second_gadget_mu1 m c - second_gadget_mu3 m c)) =
      second_gadget_gamma n m * second_gadget_gamma n m * c * c * dot a 1 := by
  simp only [dot, sqVec, second_gadget_mu1, second_gadget_mu3, Pi.sub_apply,
    Pi.one_apply, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring
end CSeparatedNPComplete
