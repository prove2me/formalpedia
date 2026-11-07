-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_riskProcess_eq_postpayment_reserve_lebesgue_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T07:32:34.278428+00:00
-- url     : https://prove2.me/submissions/8845bf6e-3301-4cd5-8b61-4071de6a1e95

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_rightJump_support_countable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) :
    ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ), 0 ≤ t →
      riskProcess X x D t.toNNReal ω =
        x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω := by
  have hcount : Set.Countable {t : ℝ | 0 ≤ t ∧
      rightLimit D t.toNNReal ω ≠ D t.toNNReal ω} :=
    dividendStrategy_rightJump_support_countable D hD ω
  have hAE : ∀ᵐ (t : ℝ) ∂(volume : Measure ℝ),
      t ∉ {s : ℝ | 0 ≤ s ∧
        rightLimit D s.toNNReal ω ≠ D s.toNNReal ω} :=
    hcount.ae_notMem (volume : Measure ℝ)
  filter_upwards [hAE] with t ht hnonneg
  have hzero : rightLimit D t.toNNReal ω = D t.toNNReal ω := by
    by_contra h
    exact ht ⟨hnonneg, h⟩
  have h :=
    (avram_wave7_18_original_riskProcess_postpayment_rightjump_decomposition
      X x D hD ω t.toNNReal).2
  simpa [hzero] using h
