-- Prove2me | solution 1 for CSeparatedNPComplete.second_gadget_12_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:59.11518+00:00
-- url     : https://prove2.me/submissions/4535069f-89ff-4b7b-8911-4a8d1d3ee2f8

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
theorem _root_.solution {n : ℕ} (m c : ℝ) (a s : Vec n) :
    dot a (sqVec (second_gadget_mu1 m c - second_gadget_mu2 m c s)) =
      second_gadget_gamma n m * second_gadget_gamma n m *
        m * m * dot a (sqVec (fun i => Real.sqrt (s i))) := by
  simp only [dot, sqVec, second_gadget_mu1, second_gadget_mu2, Pi.sub_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring
end CSeparatedNPComplete
