-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_C1_standing_candidate_nearzero_negative_mark_loss_below_top_of_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:16:20.906581+00:00
-- url     : https://prove2.me/submissions/b810305f-551b-4dbc-b74a-fb04431d63ca

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_C1_negative_jump_candidate_loss_uniform_zero_band_bound_without_zero_boundary_value
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw0 : 0 ≤ w 0) (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (ε : ℝ) (hε : 0 < ε) (hεC : ENNReal.ofReal ε < C) :
    ∀ y ∈ Ioc (0 : ℝ) ε, ∀ z : ℝ, z < 0 →
      0 ≤ w y - w (y + z) ∧ w y - w (y + z) ≤ w ε := by
  have hBound : C = ⊤ ∨ ε ≤ C.toReal := by
    by_cases htop : C = ⊤
    · exact Or.inl htop
    · exact Or.inr
        ((ENNReal.ofReal_le_iff_le_toReal htop).mp hεC.le)
  have hMono :=
    avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
      C hC w hw_cont hw_smooth hw_grad ε hBound
  exact avram_bva_a22_original_C1_negative_jump_candidate_loss_uniform_zero_band_bound_without_zero_boundary_value
    w hw_neg hw0 ε hε hMono
