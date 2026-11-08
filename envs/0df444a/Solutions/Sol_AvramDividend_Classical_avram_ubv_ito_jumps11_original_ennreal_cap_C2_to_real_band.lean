-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_ito_jumps11_original_ennreal_cap_C2_to_real_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:36:31.901103+00:00
-- url     : https://prove2.me/submissions/c81c6ed5-e2e0-4de3-a1ad-89a6c707c775

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem solution
    (C : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcC : ENNReal.ofReal c ≤ C)
    (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ContDiffOn ℝ 2 w (Ioo (0 : ℝ) c) := by
  apply hw.mono
  intro y hy
  rcases mem_Ioo.mp hy with ⟨hy0, hyc⟩
  exact ⟨hy0, lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hc).2 hyc) hcC⟩
