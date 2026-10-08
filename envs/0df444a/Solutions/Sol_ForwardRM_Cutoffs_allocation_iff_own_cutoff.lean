-- Prove2me | solution 1 for ForwardRM.Cutoffs.allocation_iff_own_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:39:43.238828+00:00
-- url     : https://prove2.me/submissions/8202174b-61f0-41fb-a16b-51f992a586d5

import Mathlib

theorem solution (k : ℕ) (y x : ℕ → ℝ)
    (hy : AntitoneOn y (Set.Icc 1 k)) (hx : AntitoneOn x (Set.Icc 1 k))
    (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) :
    (∀ ℓ, j ≤ ℓ → ℓ ≤ k → x ℓ ≤ y (k - ℓ + 1)) ↔ x j ≤ y (k - j + 1) := by
  constructor
  · intro h
    exact h j le_rfl hjk
  · intro h ℓ hjl hlk
    have h1 : x ℓ ≤ x j :=
      hx (Set.mem_Icc.mpr ⟨hj, hjk⟩) (Set.mem_Icc.mpr ⟨le_trans hj hjl, hlk⟩) hjl
    have h2 : y (k - j + 1) ≤ y (k - ℓ + 1) :=
      hy (Set.mem_Icc.mpr ⟨by omega, by omega⟩) (Set.mem_Icc.mpr ⟨by omega, by omega⟩)
        (by omega)
    linarith

