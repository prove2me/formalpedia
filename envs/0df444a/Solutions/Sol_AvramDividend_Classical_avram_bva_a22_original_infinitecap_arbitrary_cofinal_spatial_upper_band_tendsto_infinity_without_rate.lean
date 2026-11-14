-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_infinitecap_arbitrary_cofinal_spatial_upper_band_tendsto_infinity_without_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T10:54:01.80104+00:00
-- url     : https://prove2.me/submissions/3c67c345-f04f-4631-9ae3-694a9cdabb6b

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
    (C : ℝ≥0∞) (hTop : C = ⊤)
    (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    Tendsto b atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro M
  let y : ℝ := max (1 : ℝ) (M + 1)
  have hypos : 0 < y :=
    lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hycap : ENNReal.ofReal y < C := by
    simp [hTop]
  obtain ⟨N, hN⟩ := hcover y hypos hycap
  filter_upwards [eventually_ge_atTop N] with n hn
  have hbn : y ≤ b n := (hN n hn).2
  have hMy : M ≤ y :=
    le_trans (by linarith) (le_max_right _ _)
  exact le_trans hMy hbn
