-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_finite_horizon_zero_cap_spatial_ito_to_ruin_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T06:48:28.059372+00:00
-- url     : https://prove2.me/submissions/2cbdc364-dc54-4f16-b9cd-026f494ab166

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_killed_boundary_interior_ito_budget_to_ruin_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
/-- A full real-time zero/cap spatial budget controls its killed support and the ruin cash. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x T : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (hStrategy : IsDividendStrategy 𝓕 D)
    (hxc : ENNReal.ofReal x ≤ C)
    (lower : ℕ → ℝ) (upper : ℕ → ℝ≥0∞)
    (hlower : Filter.Tendsto lower Filter.atTop (𝓝 0))
    (hupper : Filter.Tendsto upper Filter.atTop (𝓝 C))
    (budget : ℝ≥0∞)
    (hBudget : ∀ n,
      (∫⁻ ω, (∫⁻ t in
        {t : ℝ | (0 ≤ t ∧ (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C)) ∧ t ≤ T} ∪
        {t : ℝ | (0 ≤ t ∧ lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n) ∧ t ≤ T},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  apply avram_wave7_19_original_killed_boundary_interior_ito_budget_to_ruin_cash
    X q x T C D hD hStrategy hxc lower upper hlower hupper budget
  intro n
  have hpoint : ∀ ω, (∫⁻ t in
      {t : ℝ | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
        (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨
        ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C)} ∪
      {t : ℝ | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
        lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧
        ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      (∫⁻ t in
      {t : ℝ | (0 ≤ t ∧ (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨
        ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C)) ∧ t ≤ T} ∪
      {t : ℝ | (0 ≤ t ∧ lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧
        ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n) ∧ t ≤ T},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
    intro ω
    apply lintegral_mono_set
    intro t ht
    rcases ht with hb | hi
    · exact Or.inl ⟨⟨hb.1.1, hb.2.2⟩, hb.2.1⟩
    · exact Or.inr ⟨⟨hi.1.1, hi.2.2.1, hi.2.2.2⟩, hi.2.1⟩
  exact le_trans (lintegral_mono hpoint) (hBudget n)
