-- Prove2me | solution 1 for DedekindSubgroups.inv_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:05:53.375948+00:00
-- url     : https://prove2.me/submissions/eedeab2c-f951-4c8f-b877-35ddfcd36ad3

module
public import Definitions.Def_DedekindSubgroups_Meyer
public import Definitions.Def_DedekindSubgroups_Parity

set_option autoImplicit true
@[expose] public section
public section
open Finset Equiv
open DedekindSubgroups
variable {h h' k : ℕ}
namespace DedekindSubgroups
theorem _root_.solution (h k : ℕ) : inv h k = (invSet h k).card := by
  unfold inv invSet
  rw [card_filter, sum_product, sum_comm]
  refine sum_congr rfl ?_
  intro y hy
  rw [mem_range] at hy
  dsimp only
  have : (range k).filter (fun x => x < y ∧ sig h k y < sig h k x)
      = (range y).filter (fun x => sig h k y < sig h k x) := by
    ext x; simp only [mem_filter, mem_range]; constructor
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩
  conv_rhs => rw [← sum_filter, this]
  rw [sum_filter]
end DedekindSubgroups
