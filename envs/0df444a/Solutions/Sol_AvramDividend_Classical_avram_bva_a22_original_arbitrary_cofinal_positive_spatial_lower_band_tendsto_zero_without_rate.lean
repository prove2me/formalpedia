-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:00:18.387199+00:00
-- url     : https://prove2.me/submissions/7487d56a-4b45-443b-88ec-3bb9e6b9dd66

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (C : ℝ≥0∞) (hC : 0 < C)
    (a b : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    Tendsto a atTop (𝓝 (0 : ℝ)) := by
  have hbase : ENNReal.ofReal (a 0) < C := by
    have hm : a 0 ∈ Icc (a 0 / 2) (b 0) :=
      ⟨by linarith [ha 0], hab 0⟩
    exact (hinside 0 hm).2
  apply tendsto_order.2
  constructor
  · intro e he
    exact Filter.Eventually.of_forall (fun n =>
      lt_trans he (ha n))
  · intro e he
    let y : ℝ := min (a 0) (e / 2)
    have hypos : 0 < y := lt_min (ha 0) (by linarith)
    have hycap : ENNReal.ofReal y < C :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (min_le_left _ _)) hbase
    obtain ⟨N, hN⟩ := hcover y hypos hycap
    filter_upwards [eventually_ge_atTop N] with n hn
    have han : a n ≤ y := (hN n hn).1
    have hye : y ≤ e / 2 := min_le_right _ _
    linarith
