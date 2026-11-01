-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_complete_discounted_stieltjes_reward_finite_horizon_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:17:15.644641+00:00
-- url     : https://prove2.me/submissions/fa7f3239-6df0-466d-953f-1f083ae2d7a4

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- For the complete genuine dividend measure, discounting and stopping
can only decrease the total finite-horizon Stieltjes reward. This includes
the time-zero payment and every continuous and right-atomic component. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) :
    (∫⁻ s in paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) ≤
      ENNReal.ofReal (rightLimit D T ω) := by
  let E : Set ℝ := paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ)
  let W : Set ℝ := Icc (0 : ℝ) (T : ℝ)
  let f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-q * s))
  have hEmeas : MeasurableSet E :=
    (paymentTimes_measurable τ).inter measurableSet_Icc
  have hWmeas : MeasurableSet W := measurableSet_Icc
  have hPoint (s : ℝ) :
      E.indicator f s ≤ W.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) s := by
    by_cases hs : s ∈ E
    · have hsW : s ∈ W := hs.2
      rw [indicator_of_mem hs, indicator_of_mem hsW]
      have hs0 : (0 : ℝ) ≤ s := hsW.1
      have hnonneg : 0 ≤ q * s := mul_nonneg hq hs0
      have hNeg : (-q) * s ≤ (0 : ℝ) := by
        simpa only [neg_mul] using (neg_nonpos.mpr hnonneg)
      have hExp : Real.exp (-q * s) ≤ (1 : ℝ) := by
        exact Real.exp_le_one_iff.mpr hNeg
      change ENNReal.ofReal (Real.exp (-q * s)) ≤ (1 : ℝ≥0∞)
      simpa using (ENNReal.ofReal_le_ofReal hExp)
    · simp [Set.indicator, hs]
  calc
    (∫⁻ s in paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) =
        (∫⁻ s : ℝ, E.indicator f s ∂dividendMeasure D ω) := by
          simp only [E, f, lintegral_indicator hEmeas]
    _ ≤ (∫⁻ s : ℝ,
        W.indicator (fun _ : ℝ => (1 : ℝ≥0∞)) s
          ∂dividendMeasure D ω) := lintegral_mono hPoint
    _ = (dividendMeasure D ω) W := by
      rw [lintegral_indicator hWmeas]
      simp
    _ = ENNReal.ofReal (rightLimit D T ω) := by
      exact avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit D hD ω T
