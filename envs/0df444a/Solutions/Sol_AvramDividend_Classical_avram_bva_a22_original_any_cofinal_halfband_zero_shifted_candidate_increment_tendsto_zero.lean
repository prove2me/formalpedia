-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_any_cofinal_halfband_zero_shifted_candidate_increment_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:27:17.562762+00:00
-- url     : https://prove2.me/submissions/674d8925-e454-4a07-aa14-852eb9a32571

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    Tendsto (fun n => w (a n / 2) - w 0)
      atTop (𝓝 (0 : ℝ)) := by
  have hLower :=
    avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
      C hC a b ha hab hinside hcover
  have hHalf : Tendsto (fun n => a n / 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [zero_div] using hLower.div_const (2 : ℝ)
  have hInside : Tendsto (fun n => a n / 2) atTop (𝓝[Ici 0] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact hHalf
    · exact Filter.Eventually.of_forall (fun n =>
        show 0 ≤ a n / 2 from div_nonneg (le_of_lt (ha n)) (by norm_num))
  have hContinuous : ContinuousWithinAt w (Ici (0 : ℝ)) 0 :=
    hw_cont 0 (by simp)
  have hValue : Tendsto (fun n => w (a n / 2)) atTop (𝓝 (w 0)) :=
    hContinuous.tendsto.comp hInside
  have hConstant : Tendsto (fun _ : ℕ => w 0) atTop (𝓝 (w 0)) :=
    tendsto_const_nhds
  have hDifference : Tendsto (fun n => w (a n / 2) - w 0)
      atTop (𝓝 (w 0 - w 0)) := hValue.sub hConstant
  simpa only [sub_self] using hDifference
