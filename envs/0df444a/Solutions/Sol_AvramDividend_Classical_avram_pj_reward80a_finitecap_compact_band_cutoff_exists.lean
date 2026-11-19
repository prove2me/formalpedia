-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward80a_finitecap_compact_band_cutoff_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T23:12:05.026198+00:00
-- url     : https://prove2.me/submissions/4f69cdf5-9593-4101-9c07-c3f0b6dcd8c4

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward36_finitecap_physical_C2_band_exists
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hCfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ Cband u v δ η : ℝ,
      0 < u ∧ 0 < δ ∧ δ ≤ 1 ∧ u + δ < v ∧
      0 < η ∧ η < 1 ∧ v < Cband ∧ v < C.toReal ∧
      ContDiffOn ℝ 2 w (Ioo 0 Cband) := by
  obtain ⟨Cband, u, v, δ, hu, hδ, hδone, huv, hv, hvCap, hwband⟩ :=
    AvramDividend.Classical.avram_pj_reward36_finitecap_physical_C2_band_exists
      C hC hCfinite w hw
  refine ⟨Cband, u, v, δ, (1 / 2 : ℝ), hu, hδ, hδone, huv, ?_, ?_, hv, hvCap, hwband⟩
  all_goals norm_num
