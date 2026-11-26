-- Prove2me | solution 1 for CSeparatedNPComplete.dot_canon_e_le_dot_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:52:04.017355+00:00
-- url     : https://prove2.me/submissions/eeef6040-0797-4755-8ebc-5752100ec93e

module
public import Definitions.Def_CSeparatedNPComplete_PartitionDefs
public import Mathlib.Tactic
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Theorems.Thm_CSeparatedNPComplete_dot_mono_right

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (a : Vec n) (i : Nat)
    (ha : is_vec_leq 0 a) : dot a (canon_e i) ≤ dot a 1 := by
  apply dot_mono_right ha
  intro j
  simp only [canon_e]
  split_ifs <;> norm_num
end CSeparatedNPComplete
