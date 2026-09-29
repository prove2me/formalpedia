-- Prove2me | solution 1 for FamousTheorems.los_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:22:10.424118+00:00
-- url     : https://prove2.me/submissions/23a9e501-dd01-4058-9d8e-c4fbdbf871f9

import Mathlib

open FirstOrder FirstOrder.Language

theorem solution {α : Type*} {M : α → Type*} {u : Ultrafilter α} {L : Language} [∀ a, L.Structure (M a)]
    [∀ a, Nonempty (M a)] (φ : L.Sentence) :
    (u : Filter α).Product M ⊨ φ ↔ ∀ᶠ a in (u : Filter α), M a ⊨ φ :=
  Ultraproduct.sentence_realize φ
