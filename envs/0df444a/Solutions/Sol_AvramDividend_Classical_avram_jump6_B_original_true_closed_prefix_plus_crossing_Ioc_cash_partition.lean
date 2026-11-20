-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_true_closed_prefix_plus_crossing_Ioc_cash_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T20:02:19.55585+00:00
-- url     : https://prove2.me/submissions/a8abdc20-eb25-483b-bcce-f50cbb22e557

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_paymentTimes_measurableSet
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (a b : ℝ) (hab : a ≤ b) :
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic b,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic a,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Ioc a b,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by
  let S : Set ℝ := paymentTimes (ruinTime X x D ω)
  let A : Set ℝ := S ∩ Iic a
  let B : Set ℝ := S ∩ Ioc a b
  have hpaid : MeasurableSet S :=
    avram_p4_d_dividend_original_paymentTimes_measurableSet _
  have hB : MeasurableSet B := hpaid.inter measurableSet_Ioc
  have hdis : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro s hsA hsB
    exact (not_lt_of_ge hsA.2) hsB.2.1
  have hunion : A ∪ B = S ∩ Iic b := by
    ext s
    constructor
    · intro hs
      rcases hs with hsa | hsb
      · exact ⟨hsa.1, le_trans hsa.2 hab⟩
      · exact ⟨hsb.1, Set.mem_Iic.mpr hsb.2.2⟩
    · intro hs
      by_cases hle : s ≤ a
      · exact Or.inl ⟨hs.1, hle⟩
      · exact Or.inr ⟨hs.1, lt_of_not_ge hle, hs.2⟩
  change (∫⁻ s in S ∩ Iic b,
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
      (∫⁻ s in A,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
      (∫⁻ s in B,
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω))
  rw [← hunion]
  exact lintegral_union hB hdis
