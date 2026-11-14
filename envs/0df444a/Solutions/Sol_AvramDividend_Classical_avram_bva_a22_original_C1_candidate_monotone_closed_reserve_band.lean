-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:17:23.751316+00:00
-- url     : https://prove2.me/submissions/2f6e32f3-cd93-4755-b81b-142d602f19b4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_allcap_linear_monotone_nonnegative
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (B : ℝ) (hBC : C = ⊤ ∨ B ≤ C.toReal) :
    MonotoneOn w (Icc (0 : ℝ) B) := by
  have hGlobal :=
    avram_p3_bv_allcap_linear_monotone_nonnegative
      C hC w hw_cont hw_smooth hw_grad
  intro y hy z hz hyz
  have hF := hGlobal (mem_Ici.mpr hy.1) (mem_Ici.mpr hz.1) hyz
  rcases hBC with htop | hcap
  · simpa only [htop, if_true] using hF
  · by_cases htop : C = ⊤
    · simpa only [htop, if_true] using hF
    · have hyCap : y ≤ C.toReal := hy.2.trans hcap
      have hzCap : z ≤ C.toReal := hz.2.trans hcap
      simpa only [if_neg htop, if_pos hyCap, if_pos hzCap] using hF
