-- Prove2me | solution 1 for FamousTheorems.neumann_coset_cover_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:20:27.527523+00:00
-- url     : https://prove2.me/submissions/3fff06b6-31da-4920-a6f6-19d17ba5bf22

import Mathlib

open Pointwise

theorem solution {G ι : Type*} [Group G] {H : ι → Subgroup G} {g : ι → G} {s : Finset ι}
    (hcovers : ⋃ i ∈ s, g i • (H i : Set G) = Set.univ) :
    ∃ i ∈ s, (H i).FiniteIndex ∧ (H i).index ≤ s.card :=
  Subgroup.exists_index_le_card_of_leftCoset_cover hcovers
