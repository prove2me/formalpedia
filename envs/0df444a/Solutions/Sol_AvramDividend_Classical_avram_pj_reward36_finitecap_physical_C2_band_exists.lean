-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward36_finitecap_physical_C2_band_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T15:58:41.599316+00:00
-- url     : https://prove2.me/submissions/d1b47202-0954-4121-a9b0-656ce959b6bd

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ Cband u v δ : ℝ,
      0 < u ∧ 0 < δ ∧ δ ≤ 1 ∧ u + δ < v ∧
      v < Cband ∧ v < C.toReal ∧
      ContDiffOn ℝ 2 w (Ioo 0 Cband) := by
  have hpos : 0 < C.toReal := ENNReal.toReal_pos (ne_of_gt hC) hCfinite
  let δ : ℝ := min (C.toReal / 16) (1 / 2)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ 1 := by
    dsimp [δ]
    calc
      min (C.toReal / 16) (1 / 2) ≤ (1 / 2 : ℝ) := min_le_right _ _
      _ ≤ 1 := by norm_num
  have hδub : δ ≤ C.toReal / 16 := by
    dsimp [δ]
    exact min_le_left _ _
  refine ⟨C.toReal / 2, C.toReal / 16, C.toReal / 4, δ,
    by positivity, hδ, hδ1, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · apply hw.mono
    intro y hy
    rcases mem_Ioo.mp hy with ⟨hy0, hyb⟩
    change 0 < y ∧ ENNReal.ofReal y < C
    refine ⟨hy0, (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hy0) hCfinite).2 ?_⟩
    linarith
