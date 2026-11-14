-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb32_original_zero_reserve_linear_source_forces_nonnegative_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T11:31:06.421443+00:00
-- url     : https://prove2.me/submissions/dbd3df18-c36c-41e4-b2da-f97cfb9f8364

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb24_original_zero_reserve_nojump_source_dividend_exact_physical_linear_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (S : ℝ≥0) (hS : 0 < S)
    (hZero : ∀ t : ℝ≥0, t ≤ S → riskProcess X x D t ω = 0)
    (hSource : ∀ t : ℝ≥0, t ≤ S →
      X.X t ω = (t : ℝ) * X.drift) :
    0 ≤ X.drift  := by
  have hStrat : IsDividendStrategy 𝓕 D := hD.1.1
  have hD0 : D 0 ω = 0 := hStrat.1 ω
  have hMono : Monotone (fun t : ℝ≥0 => D t ω) := hStrat.2.1 ω
  have hDS := avram_bvb24_original_zero_reserve_nojump_source_dividend_exact_physical_linear_drift
    X x C D hD ω S hZero hSource S le_rfl
  have hVal : 0 ≤ (S : ℝ) * X.drift := by
    have hPay : D 0 ω ≤ D S ω := hMono (show (0 : ℝ≥0) ≤ S from zero_le)
    simpa only [hD0, hDS] using hPay
  have hSReal : 0 < (S : ℝ) := NNReal.coe_pos.mpr hS
  rw [mul_comm (S : ℝ) X.drift] at hVal
  exact nonneg_of_mul_nonneg_left hVal hSReal
