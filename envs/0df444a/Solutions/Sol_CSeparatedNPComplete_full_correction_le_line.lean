-- Prove2me | solution 1 for CSeparatedNPComplete.full_correction_le_line
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:20.483599+00:00
-- url     : https://prove2.me/submissions/4b75eee3-cbc5-4031-89e2-0e53044a4edc

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
public import Theorems.Thm_CSeparatedNPComplete_inv_one_plus_le_line
section
@[expose] public section
namespace CSeparatedNPComplete
private theorem sum_line {n : Nat} (a : Vec n) :
    (∑ i, (1 - a i / 2)) = (n : ℝ) - dot a 1 / 2 := by
  simp [Finset.sum_sub_distrib, Finset.sum_div, dot]
end CSeparatedNPComplete
end
end

set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (a : Vec n) (ha : box_constraints a) :
    (∑ i, (1 + a i)⁻¹) ≤ (n : ℝ) - dot a 1 / 2 := by
  rw [← sum_line]
  exact Finset.sum_le_sum fun i _ => inv_one_plus_le_line (a i) ⟨ha.1 i, ha.2 i⟩
end CSeparatedNPComplete
