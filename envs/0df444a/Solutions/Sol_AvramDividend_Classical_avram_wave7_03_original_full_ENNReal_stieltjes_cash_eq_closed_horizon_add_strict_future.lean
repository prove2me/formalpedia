-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_full_ENNReal_stieltjes_cash_eq_closed_horizon_add_strict_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:44:39.920128+00:00
-- url     : https://prove2.me/submissions/64df555c-228c-4a62-a2cc-8fd1684e3b8e

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Complete original discounted Stieltjes cash splits into the closed
    stopped-horizon payout and strictly future payout, with horizon atoms
    belonging to the closed window and no finiteness premise. -/
/- W7-03 fresh source snapshot: exact original-measure proof body preserved. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (q T : ℝ) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioi T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  let A : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Iic T
  let B : Set ℝ := paymentTimes (ruinTime X x D ω) ∩ Ioi T
  have hB : MeasurableSet B :=
    (paymentTimes_measurable (ruinTime X x D ω)).inter measurableSet_Ioi
  have hDisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro t htA htB
    have hle : t ≤ T := mem_Iic.mp htA.2
    have hlt : T < t := mem_Ioi.mp htB.2
    exact (not_lt_of_ge hle) hlt
  have hUnion : A ∪ B = paymentTimes (ruinTime X x D ω) := by
    ext t
    simp only [A, B, mem_union, mem_inter_iff, mem_Iic, mem_Ioi]
    constructor
    · rintro (⟨ht, _⟩ | ⟨ht, _⟩)
      · exact ht
      · exact ht
    · intro ht
      by_cases hT : t ≤ T
      · exact Or.inl ⟨ht, hT⟩
      · exact Or.inr ⟨ht, lt_of_not_ge hT⟩
  calc
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in A ∪ B,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
          rw [hUnion]
    _ =
      (∫⁻ t in A,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in B,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) :=
      lintegral_union hB hDisj
    _ = _ := rfl
