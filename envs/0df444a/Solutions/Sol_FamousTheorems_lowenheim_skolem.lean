-- Prove2me | solution 1 for FamousTheorems.lowenheim_skolem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:58:30.27362+00:00
-- url     : https://prove2.me/submissions/8fd97ba8-c6e2-4ec7-b41a-e4aa8e8ca9c3

import Mathlib

universe u v w w'

theorem solution (L : FirstOrder.Language.{u, v}) (M : Type w') [L.Structure M] [Infinite M] (κ : Cardinal.{w})
    (h1 : Cardinal.aleph0 ≤ κ) (h2 : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ N : CategoryTheory.Bundled.{w} L.Structure,
      (Nonempty (L.ElementaryEmbedding N M) ∨ Nonempty (L.ElementaryEmbedding M N)) ∧ Cardinal.mk N = κ :=
  FirstOrder.Language.exists_elementaryEmbedding_card_eq L M κ h1 h2
