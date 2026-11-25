-- Prove2me | solution 1 for DedekindSubgroups.sum_pairs_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:01:46.640798+00:00
-- url     : https://prove2.me/submissions/c100bf35-f497-496a-94f6-8674fee38a50

module
public import Mathlib
public import Definitions.Def_DedekindSubgroups_Basic

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution (g : ℕ → ℤ) (m : ℕ) :
    ∑ y ∈ range m, ∑ _x ∈ range y, g y = ∑ y ∈ range m, (y : ℤ) * g y := by
  refine Finset.sum_congr rfl ?_
  intro y _
  simp [sum_const, card_range]
end DedekindSubgroups
