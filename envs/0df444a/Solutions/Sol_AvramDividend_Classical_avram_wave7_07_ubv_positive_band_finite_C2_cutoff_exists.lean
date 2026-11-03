-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_ubv_positive_band_finite_C2_cutoff_exists
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:49:00.375407+00:00
-- url     : https://prove2.me/submissions/8b13847b-41a3-449a-a6ac-14150fd5f5ef

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_extended_cap_finite_real_padding_exists
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_ubv_extended_cap_local_C2_restrict

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞) (v : ℝ)
    (hv0 : 0 ≤ v) (hvC : ENNReal.ofReal v < C)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ R : ℝ, v < R ∧ ENNReal.ofReal R < C ∧
      ContDiffOn ℝ 2 w (Ioo 0 R) := by
  obtain ⟨R, hvR, hRC⟩ :=
    avram_wave7_07_extended_cap_finite_real_padding_exists C v hv0 hvC
  refine ⟨R, hvR, hRC, ?_⟩
  exact avram_wave7_07_ubv_extended_cap_local_C2_restrict w C hw R hRC
