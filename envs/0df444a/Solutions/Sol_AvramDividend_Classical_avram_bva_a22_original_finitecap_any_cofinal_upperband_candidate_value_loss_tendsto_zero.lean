-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_finitecap_any_cofinal_upperband_candidate_value_loss_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:25:46.258767+00:00
-- url     : https://prove2.me/submissions/7e7b646c-ae75-409d-893d-b13986e7f237

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_finitecap_arbitrary_cofinal_spatial_upper_band_tendsto_cap_without_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (C : ℝ≥0∞) (L : ℝ) (hL : 0 < L)
    (hCL : C = ENNReal.ofReal L)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici (0 : ℝ)))
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    Tendsto (fun n => w L - w (b n)) atTop (𝓝 (0 : ℝ)) := by
  have hb :=
    avram_bva_a22_original_finitecap_arbitrary_cofinal_spatial_upper_band_tendsto_cap_without_rate
      C L hL hCL a b ha hab hinside hcover
  have hbWithin : Tendsto b atTop (𝓝[Ici 0] L) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · exact hb
    · exact Filter.Eventually.of_forall (fun n =>
        show 0 ≤ b n from le_trans (le_of_lt (ha n)) (hab n))
  have hw : ContinuousWithinAt w (Ici (0 : ℝ)) L :=
    hw_cont L (by simp [le_of_lt hL])
  have hValue : Tendsto (fun n => w (b n)) atTop (𝓝 (w L)) :=
    hw.tendsto.comp hbWithin
  have hConstant : Tendsto (fun _ : ℕ => w L) atTop (𝓝 (w L)) :=
    tendsto_const_nhds
  have hDifference : Tendsto (fun n => w L - w (b n))
      atTop (𝓝 (w L - w L)) := hConstant.sub hValue
  simpa only [sub_self] using hDifference
