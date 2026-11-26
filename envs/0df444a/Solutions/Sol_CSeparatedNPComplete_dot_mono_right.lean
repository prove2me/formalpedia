-- Prove2me | solution 1 for CSeparatedNPComplete.dot_mono_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:51:13.024119+00:00
-- url     : https://prove2.me/submissions/99b9de4f-ed97-445b-88f8-5ccae0c1e24e

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} {a u v : Vec n}
    (ha : is_vec_leq 0 a) (huv : is_vec_leq u v) : dot a u ≤ dot a v :=
  Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (huv i) (ha i)
end CSeparatedNPComplete
