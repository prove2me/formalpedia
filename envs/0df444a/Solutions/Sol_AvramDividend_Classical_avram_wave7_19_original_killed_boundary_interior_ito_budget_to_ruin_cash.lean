-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_killed_boundary_interior_ito_budget_to_ruin_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T00:19:49.680998+00:00
-- url     : https://prove2.me/submissions/b096f950-a25a-4761-845c-f6a55dbd2e26

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_killed_cutoff_liminf_ito_to_ruin_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
/-- Each-cutoff killed cash budgets imply the liminf budget and full ruin cash. -/
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
        {t : ℝ | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
          (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C)} ∪
        {t : ℝ | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
          lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧
          ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n},
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget) :
    (∫⁻ ω, (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P) ≤ budget := by
  let f : ℕ → ℝ≥0∞ := fun n =>
    ∫⁻ ω, (∫⁻ t in
      {t : ℝ | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
        (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω = 0 ∨
         ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) = C)} ∪
      {t : ℝ | t ∈ paymentTimes (ruinTime X x D ω) ∧ t ≤ T ∧
        lower n < x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω ∧
        ENNReal.ofReal (x + X.X t.toNNReal ω - rightLimit D t.toNNReal ω) < upper n},
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ∂P
  have hf : ∀ n, f n ≤ budget := by
    intro n
    exact hBudget n
  have hle : Filter.liminf f Filter.atTop ≤
      Filter.liminf (fun _ : ℕ => budget) Filter.atTop :=
    Filter.liminf_le_liminf (Filter.Eventually.of_forall hf)
  have hlim : Filter.liminf f Filter.atTop ≤ budget := by
    simpa only [Filter.liminf_const] using hle
  apply avram_wave7_19_original_killed_cutoff_liminf_ito_to_ruin_cash
    X q x T C D hD hStrategy hxc lower upper hlower hupper budget
  exact hlim
