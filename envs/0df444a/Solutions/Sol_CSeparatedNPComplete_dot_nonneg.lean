-- Prove2me | solution 1 for CSeparatedNPComplete.dot_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:51:11.291066+00:00
-- url     : https://prove2.me/submissions/41e75720-d801-42a6-af7a-d517c4a2a280

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} {a v : Vec n}
    (ha : is_vec_leq 0 a) (hv : is_vec_leq 0 v) : 0 ≤ dot a v :=
  Finset.sum_nonneg fun i _ => mul_nonneg (ha i) (hv i)
end CSeparatedNPComplete
