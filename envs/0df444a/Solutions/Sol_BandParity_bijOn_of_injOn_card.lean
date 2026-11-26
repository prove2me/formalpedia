-- Prove2me | solution 1 for BandParity.bijOn_of_injOn_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:04:47.625984+00:00
-- url     : https://prove2.me/submissions/79e5e216-23b4-4c73-97ad-11709f06b663

module
public import Definitions.Def_BandParity_Laws
public import Definitions.Def_BandParity_Main

set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
omit hp
namespace BandParity
theorem _root_.solution {α β : Type*} [DecidableEq β] {s : Finset α} {t : Finset β}
    {f : α → β} (hm : Set.MapsTo f s t) (hi : Set.InjOn f s) (hc : t.card ≤ s.card) :
    Set.BijOn f s t := by
  refine ⟨hm, hi, fun y hy => ?_⟩
  have hsub : s.image f ⊆ t := fun y hy => by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy; exact hm hx
  have heq : s.image f = t :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hi]; exact hc)
  have hy' : y ∈ s.image f := by rw [heq]; exact hy
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy'
  exact ⟨x, hx, rfl⟩
end BandParity
