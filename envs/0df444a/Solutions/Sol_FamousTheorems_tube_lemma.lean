-- Prove2me | solution 1 for FamousTheorems.tube_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:09:14.580891+00:00
-- url     : https://prove2.me/submissions/96110e10-6932-48f7-b71d-a6da74aeae78

import Mathlib

theorem solution {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s : Set X} {t : Set Y} {n : Set (X × Y)}
    (hs : IsCompact s) (ht : IsCompact t) (hn : IsOpen n) (hp : s ×ˢ t ⊆ n) :
    ∃ (u : Set X) (v : Set Y), IsOpen u ∧ IsOpen v ∧ s ⊆ u ∧ t ⊆ v ∧ u ×ˢ v ⊆ n :=
  generalized_tube_lemma hs ht hn hp
