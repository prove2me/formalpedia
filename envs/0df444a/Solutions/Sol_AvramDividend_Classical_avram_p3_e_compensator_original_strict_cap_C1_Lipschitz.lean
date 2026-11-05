-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_original_strict_cap_C1_Lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:42:53.051736+00:00
-- url     : https://prove2.me/submissions/c7750647-ac2f-44a1-816f-12b82e47a012

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_C1_open_interior_Lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_source_HJB_strict_cap_band_open
open MeasureTheory Set Topology AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
(C : ℝ≥0∞) (w : ℝ → ℝ) (a b : ℝ)
(ha : 0 < a) (hab : a ≤ b) (hbC : ENNReal.ofReal b < C)
(hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
∃ L : ℝ, 0 ≤ L ∧
  ∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
    |w u - w v| ≤ L * |u - v| := by
  obtain ⟨hUopen, hsub⟩ :=
    avram_p3_e_compensator_source_HJB_strict_cap_band_open C a b ha hab hbC
  have hhalf : a / 2 ≤ b := by linarith
  exact avram_p3_e_compensator_original_C1_open_interior_Lipschitz
    w a b hhalf _ hUopen hw_smooth hsub
