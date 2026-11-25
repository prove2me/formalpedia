-- Prove2me | solution 1 for DedekindSubgroups.mem_zpowers_of_orderOf_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:11:18.900805+00:00
-- url     : https://prove2.me/submissions/4add1f33-2f7e-4f93-b7f8-10d8fe1776e0

module
public import Definitions.Def_DedekindSubgroups_Prime
public import Definitions.Def_DedekindSubgroups_Optimality

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution {u x : (ZMod 63)ˣ} (hu : orderOf u = 3) :
    x ∈ Subgroup.zpowers u ↔ x ∈ ({1, u, u ^ 2} : Finset (ZMod 63)ˣ) := by
  rw [mem_zpowers_iff_mem_range_orderOf, hu]
  simp only [mem_image, mem_range, mem_insert, mem_singleton]
  constructor
  · rintro ⟨i, hi, rfl⟩
    interval_cases i <;> simp
  · rintro (h | h | h) <;> rw [h]
    · exact ⟨0, by norm_num, pow_zero u⟩
    · exact ⟨1, by norm_num, pow_one u⟩
    · exact ⟨2, by norm_num, rfl⟩
end DedekindSubgroups
