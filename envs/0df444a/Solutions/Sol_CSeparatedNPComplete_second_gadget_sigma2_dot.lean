-- Prove2me | solution 1 for CSeparatedNPComplete.second_gadget_sigma2_dot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:48.391076+00:00
-- url     : https://prove2.me/submissions/45181ba7-1a04-45e0-a704-af4a23d1294f

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
    dot a (second_gadget_sigma2 m) =
      second_gadget_gamma n m * second_gadget_gamma n m * m * dot a 1 := by
  simp only [dot, second_gadget_sigma2, Pi.one_apply, mul_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring
end CSeparatedNPComplete
