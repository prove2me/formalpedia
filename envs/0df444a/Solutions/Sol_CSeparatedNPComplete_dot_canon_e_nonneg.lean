-- Prove2me | solution 1 for CSeparatedNPComplete.dot_canon_e_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:51:59.292809+00:00
-- url     : https://prove2.me/submissions/47ed742b-b96f-4834-8c7a-abf237fd7e98

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Theorems.Thm_CSeparatedNPComplete_dot_nonneg

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (a : Vec n) (i : Nat)
    (ha : is_vec_leq 0 a) : 0 ≤ dot a (canon_e i) := by
  apply dot_nonneg ha
  intro j
  simp only [canon_e]
  split_ifs <;> norm_num
end CSeparatedNPComplete
