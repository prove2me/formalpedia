-- Prove2me | solution 1 for AvramDividend.Classical.avram_b114_original_nonzero_source_jump_iff_some_negative_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:14:02.378208+00:00
-- url     : https://prove2.me/submissions/d5e62108-6dc2-40af-98a0-f52df2356e58

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b118_original_finite_physically_marked_cells_one_cutoff
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) :
    (∃ u : ℝ≥0, s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0) ↔
    (∃ n : ℕ, ∃ u : ℝ≥0, s < u ∧ u ≤ t ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))) := by
  constructor
  · rintro ⟨u, hsu, hut, hne⟩
    have hMarked : ∀ i ∈ ({0} : Finset ℕ), ∃ v : ℝ≥0,
        (fun _ : ℕ => s) i < v ∧ v ≤ (fun _ : ℕ => t) i ∧
        X.X v ω - Function.leftLim (fun a : ℝ≥0 => X.X a ω) v ≠ 0 := by
      intro i hi
      exact ⟨u, hsu, hut, hne⟩
    obtain ⟨n, hCut⟩ :=
      avram_b118_original_finite_physically_marked_cells_one_cutoff
        X ω ({0} : Finset ℕ) (fun _ => s) (fun _ => t) hMarked
    obtain ⟨v, hsv, hvt, hBand⟩ := hCut 0 (by simp)
    exact ⟨n, v, hsv, hvt, hBand⟩
  · rintro ⟨n, u, hsu, hut, hBand⟩
    have hPos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    refine ⟨u, hsu, hut, ?_⟩
    linarith
