-- Prove2me | solution 1 for AvramDividend.Classical.discounted_dividendMeasure_Ico_partition_bracket
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T08:44:33.146001+00:00
-- url     : https://prove2.me/submissions/9cd8bb73-2200-4e73-9e17-44a503614486

import Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_Ico_ge_end_weighted_increment
import Theorems.Thm_AvramDividend_Classical_discounted_dividendMeasure_Ico_le_start_weighted_increment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q) (a b : ℝ≥0) :
    ENNReal.ofReal (Real.exp (-(q * (b : ℝ))) * (D b ω - D a ω)) ≤
      (∫⁻ s in Ico (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ∧
    (∫⁻ s in Ico (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (a : ℝ))) * (D b ω - D a ω)) := by
  exact ⟨discounted_dividendMeasure_Ico_ge_end_weighted_increment
    D hD ω q hq a b,
    discounted_dividendMeasure_Ico_le_start_weighted_increment
      D hD ω q hq a b⟩
