-- Prove2me | solution 1 for CSeparatedNPComplete.schedule_full_correction_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:25.246684+00:00
-- url     : https://prove2.me/submissions/ccac363d-0f26-4f53-93db-4d325b8bc249

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
public import Theorems.Thm_CSeparatedNPComplete_dot_canon_e_eq


set_option autoImplicit true
@[expose] public section
public section
open CSeparatedNPComplete
namespace CSeparatedNPComplete
theorem _root_.solution {n : Nat} (a : Vec n) :
    gaussian_schedule_hinge_correction a n = ∑ i, (1 + a i)⁻¹ := by
  unfold gaussian_schedule_hinge_correction
  rw [Finset.sum_range]
  simp only [dot_canon_e_eq]
end CSeparatedNPComplete
