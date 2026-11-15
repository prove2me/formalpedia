-- Prove2me | solution 1 for AvramDividend.Classical.avram_b24_unique_ruincontact_cell_on_separated_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:47:20.405254+00:00
-- url     : https://prove2.me/submissions/a43a9247-97da-460b-b7cb-f1d60f9ea4e5

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    (S : Finset ℕ) (a b : ℕ → ℝ≥0)
    (hSep : ∀ i j, i ∈ S → j ∈ S → i < j → b i ≤ a j)
    (σ : ℝ≥0) :
    ∀ i ∈ S, ∀ j ∈ S,
      a i < σ → σ ≤ b i → a j < σ → σ ≤ b j → i = j := by
  intro i hi j hj hai hbi haj hbj
  rcases lt_trichotomy i j with hij | heq | hji
  · have hSepIJ := hSep i j hi hj hij
    exact False.elim ((not_lt_of_ge (le_trans hbi hSepIJ)) haj)
  · exact heq
  · have hSepJI := hSep j i hj hi hji
    exact False.elim ((not_lt_of_ge (le_trans hbj hSepJI)) hai)
