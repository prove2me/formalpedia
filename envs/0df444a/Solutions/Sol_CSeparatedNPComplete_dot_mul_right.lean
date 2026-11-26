-- Prove2me | solution 1 for CSeparatedNPComplete.dot_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:57:35.961728+00:00
-- url     : https://prove2.me/submissions/45cd1e9c-361b-4e77-8d36-cdca699d25cf

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (a v : Vec n) (r : ℝ) :
    dot a (fun i => r * v i) = r * dot a v := by
  simp only [dot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring
end CSeparatedNPComplete
