-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_ubv_extended_cap_local_C2_restrict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:43:11.645275+00:00
-- url     : https://prove2.me/submissions/a5ded02f-ad71-467c-b087-824603726c7a

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (R : ℝ) (hRcap : ENNReal.ofReal R < C) :
    ContDiffOn ℝ 2 w (Ioo 0 R) := by
  apply hw_smooth.mono
  intro y hy
  rcases hy with ⟨hy0, hyR⟩
  exact ⟨hy0, (ENNReal.ofReal_le_ofReal hyR.le).trans_lt hRcap⟩
