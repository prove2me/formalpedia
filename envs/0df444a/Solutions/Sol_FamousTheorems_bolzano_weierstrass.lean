-- Prove2me | solution 1 for FamousTheorems.bolzano_weierstrass
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:14:53.909415+00:00
-- url     : https://prove2.me/submissions/2ec84e8b-86b4-4f3b-a902-0bd06bca8e12

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution {X : Type*} [PseudoMetricSpace X] [ProperSpace X] {s : Set X}
    (hs : Bornology.IsBounded s) {x : ℕ → X} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  tendsto_subseq_of_bounded hs hx
