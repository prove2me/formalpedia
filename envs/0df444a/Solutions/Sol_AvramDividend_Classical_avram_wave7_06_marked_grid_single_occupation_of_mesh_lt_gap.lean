-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_marked_grid_single_occupation_of_mesh_lt_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:04:07.662643+00:00
-- url     : https://prove2.me/submissions/8f734ba3-d828-447b-890e-d354ffddd4f2

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
open scoped NNReal

/-- A mesh finer than the source finite marked-time gap has at most one jump per cell. -/
theorem solution
    (F : Finset ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (hGap : ∀ u ∈ F, ∀ v ∈ F, u ≠ v →
      δ ≤ |(u : ℝ) - (v : ℝ)|)
    (grid : ℕ → ℝ≥0) (m : ℕ)
    (hMesh : ∀ i < m, (grid (i + 1) : ℝ) - (grid i : ℝ) < δ) :
    ∀ i < m, ∀ u ∈ F, ∀ v ∈ F,
      u ∈ Set.Ioc (grid i) (grid (i + 1)) →
      v ∈ Set.Ioc (grid i) (grid (i + 1)) → u = v := by
  intro i hi u hu v hv huCell hvCell
  by_contra hne
  have hdist : δ ≤ |(u : ℝ) - (v : ℝ)| :=
    hGap u hu v hv hne
  obtain ⟨hau, hub⟩ := Set.mem_Ioc.mp huCell
  obtain ⟨hav, hvb⟩ := Set.mem_Ioc.mp hvCell
  have hauR : (grid i : ℝ) < (u : ℝ) := by exact_mod_cast hau
  have hubR : (u : ℝ) ≤ (grid (i + 1) : ℝ) := by exact_mod_cast hub
  have havR : (grid i : ℝ) < (v : ℝ) := by exact_mod_cast hav
  have hvbR : (v : ℝ) ≤ (grid (i + 1) : ℝ) := by exact_mod_cast hvb
  have hsmall1 : (u : ℝ) - (v : ℝ) < δ := by
    linarith [hMesh i hi]
  have hsmall2 : (v : ℝ) - (u : ℝ) < δ := by
    linarith [hMesh i hi]
  have hAbs : |(u : ℝ) - (v : ℝ)| < δ :=
    abs_lt.mpr ⟨by linarith, hsmall1⟩
  linarith
