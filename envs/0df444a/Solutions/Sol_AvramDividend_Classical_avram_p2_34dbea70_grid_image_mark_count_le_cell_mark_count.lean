-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_grid_image_mark_count_le_cell_mark_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:58:23.867015+00:00
-- url     : https://prove2.me/submissions/cbff3bbf-c0c3-464b-91e4-6110a4c598d5

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset

/-- A finite collection of marked grid points cannot outnumber its
marked source cells, even when two cells have the same right endpoint. -/
theorem solution {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β)
    (marked : β → Prop) [DecidablePred marked] :
    ((s.image f).filter marked).card ≤
      (s.filter (fun x => marked (f x))).card := by
  classical
  have hfilter : (s.image f).filter marked =
      (s.filter (fun x => marked (f x))).image f := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨a, ha, hfa⟩, hy⟩
      refine ⟨a, ⟨ha, ?_⟩, hfa⟩
      simpa only [hfa] using hy
    · rintro ⟨a, ⟨ha, hmark⟩, hfa⟩
      exact ⟨⟨a, ha, hfa⟩, by simpa only [hfa] using hmark⟩
  rw [hfilter]
  exact Finset.card_image_le
