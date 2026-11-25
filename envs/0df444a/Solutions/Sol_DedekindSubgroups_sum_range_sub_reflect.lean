-- Prove2me | solution 1 for DedekindSubgroups.sum_range_sub_reflect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:01:43.600465+00:00
-- url     : https://prove2.me/submissions/836259de-90fc-4e6e-bd81-e027cc088592

module
public import Mathlib
public import Definitions.Def_DedekindSubgroups_Basic

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution (f : ℕ → ℤ) (y : ℕ) :
    ∑ x ∈ range y, f (y - x) = ∑ j ∈ range y, f (j + 1) := by
  rw [← Finset.sum_range_reflect (fun j => f (j + 1)) y]
  refine Finset.sum_congr rfl ?_
  intro x hx
  simp only [mem_range] at hx
  congr 1
  omega
end DedekindSubgroups
