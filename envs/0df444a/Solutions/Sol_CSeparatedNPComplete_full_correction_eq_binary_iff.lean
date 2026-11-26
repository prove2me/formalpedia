-- Prove2me | solution 1 for CSeparatedNPComplete.full_correction_eq_binary_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:53:58.7536+00:00
-- url     : https://prove2.me/submissions/326c0114-3eef-46ef-86d2-e4101bbc3c11

module
public import Definitions.Def_CSeparatedNPComplete_PartitionBasic
public import Definitions.Def_CSeparatedNPComplete_Reciprocal
public import Theorems.Thm_CSeparatedNPComplete_inv_one_plus_le_line
public import Theorems.Thm_CSeparatedNPComplete_inv_one_plus_line_eq_binary_iff
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
    (∑ i, (1 + a i)⁻¹) = (n : ℝ) - dot a 1 / 2 ↔ is_binary a := by
  rw [← sum_line]
  constructor
  · intro he i
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)),
        0 ≤ (1 - a j / 2) - (1 + a j)⁻¹ :=
      fun j _ => sub_nonneg.mpr (inv_one_plus_le_line (a j) ⟨ha.1 j, ha.2 j⟩)
    have hsum : (∑ j, ((1 - a j / 2) - (1 + a j)⁻¹)) = 0 := by
      rw [Finset.sum_sub_distrib, he, sub_self]
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ i)
    exact (inv_one_plus_line_eq_binary_iff (a i) ⟨ha.1 i, ha.2 i⟩).mp
      (by linarith)
  · intro hb
    apply Finset.sum_congr rfl
    intro i _
    exact (inv_one_plus_line_eq_binary_iff (a i) ⟨ha.1 i, ha.2 i⟩).mpr (hb i)
end CSeparatedNPComplete
