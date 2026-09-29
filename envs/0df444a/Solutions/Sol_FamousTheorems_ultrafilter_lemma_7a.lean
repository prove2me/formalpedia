-- Prove2me | solution 1 for FamousTheorems.ultrafilter_lemma_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:55:55.702163+00:00
-- url     : https://prove2.me/submissions/644464f8-ba91-428d-b102-0a7d9c100719

import Mathlib

theorem solution {α : Type*} (f : Filter α) [f.NeBot] : ∃ u : Ultrafilter α, (u : Filter α) ≤ f :=
  Ultrafilter.exists_le f
