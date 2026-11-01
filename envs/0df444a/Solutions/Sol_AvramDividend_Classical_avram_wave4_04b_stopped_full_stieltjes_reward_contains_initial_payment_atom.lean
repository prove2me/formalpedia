-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_stopped_full_stieltjes_reward_contains_initial_payment_atom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T13:28:14.3294+00:00
-- url     : https://prove2.me/submissions/95c2090f-835a-47b5-b09a-4f8ab27ac23b

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

set_option maxHeartbeats 1000000 in
/-- The closed stopped full Stieltjes dividend reward always retains the
chronologically earliest right-payment atom at time zero, weighted by one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ) :
    ENNReal.ofReal (rightLimit D (0 : ℝ≥0) ω - D (0 : ℝ≥0) ω) ≤
      (∫⁻ s in paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) := by
  let μ : Measure ℝ := dividendMeasure D ω
  let E : Set ℝ := paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ)
  let f : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (-q * s))
  have h0payment : (0 : ℝ) ∈ paymentTimes τ := by
    simp [paymentTimes]
  have h0E : (0 : ℝ) ∈ E := by
    refine ⟨h0payment, ?_⟩
    simp
  have hEmeas : MeasurableSet E :=
    (paymentTimes_measurable τ).inter measurableSet_Icc
  have hPoint (s : ℝ) :
      ({(0 : ℝ)} : Set ℝ).indicator f s ≤ E.indicator f s := by
    by_cases hs : s = 0
    · subst s
      simp [Set.indicator, h0E]
    · have hsnot : s ∉ ({(0 : ℝ)} : Set ℝ) := by
        simpa using hs
      simp [Set.indicator, hsnot]
  have hAtom : μ {(0 : ℝ)} =
      ENNReal.ofReal (rightLimit D (0 : ℝ≥0) ω - D (0 : ℝ≥0) ω) := by
    exact dividendMeasure_singleton_eq_rightLimit_sub D hD ω (0 : ℝ≥0)
  have hOne :
      (∫⁻ s in ({(0 : ℝ)} : Set ℝ), f s ∂μ) = μ {(0 : ℝ)} := by
    rw [lintegral_singleton]
    simp [f]
  calc
    ENNReal.ofReal (rightLimit D (0 : ℝ≥0) ω - D (0 : ℝ≥0) ω) =
        μ {(0 : ℝ)} := hAtom.symm
    _ = (∫⁻ s in ({(0 : ℝ)} : Set ℝ), f s ∂μ) := hOne.symm
    _ = (∫⁻ s : ℝ, ({(0 : ℝ)} : Set ℝ).indicator f s ∂μ) := by
      rw [lintegral_indicator (measurableSet_singleton (0 : ℝ))]
    _ ≤ (∫⁻ s : ℝ, E.indicator f s ∂μ) :=
      lintegral_mono hPoint
    _ = (∫⁻ s in E, f s ∂μ) := by
      rw [lintegral_indicator hEmeas]
    _ = (∫⁻ s in paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ),
        ENNReal.ofReal (Real.exp (-q * s)) ∂dividendMeasure D ω) := by
      rfl
