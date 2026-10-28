-- Prove2me | solution 1 for AvramDividend.Classical.zeroCumulativeDividend_implies_zeroStieltjesPayoff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T17:44:40.676544+00:00
-- url     : https://prove2.me/submissions/0a7916e0-0160-4eb5-ab37-563dc03ef09e

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A strategy that accumulates no dividends anywhere along a path has
    identically zero discounted Stieltjes payoff on that path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (hzero : ∀ t : ℝ≥0, D t ω = 0) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)) = 0 := by
  let μ := dividendMeasure D ω
  have hzero_n (n : ℕ) : μ (Set.Ico (0 : ℝ) (n : ℝ)) = 0 := by
    have h := dividendMeasure_Ico_zero_eq_dividendValue D hD ω (n : ℝ≥0)
    simpa [μ, hzero (n : ℝ≥0)] using h
  have hUnion : μ (⋃ n : ℕ, Set.Ico (0 : ℝ) (n : ℝ)) = 0 := by
    have hle : μ (⋃ n : ℕ, Set.Ico (0 : ℝ) (n : ℝ)) ≤ 0 := by
      calc
        μ (⋃ n : ℕ, Set.Ico (0 : ℝ) (n : ℝ)) ≤
            ∑' n : ℕ, μ (Set.Ico (0 : ℝ) (n : ℝ)) :=
          measure_iUnion_le _
        _ = 0 := by simp [hzero_n]
    exact le_antisymm hle (by exact zero_le)
  have hsub :
      paymentTimes (ruinTime X x D ω) ⊆
        ⋃ n : ℕ, Set.Ico (0 : ℝ) (n : ℝ) := by
    intro t ht
    obtain ⟨n, hn⟩ := exists_nat_gt t
    exact Set.mem_iUnion.mpr ⟨n, ⟨ht.1, hn⟩⟩
  have hPay : μ (paymentTimes (ruinTime X x D ω)) = 0 := by
    have hle : μ (paymentTimes (ruinTime X x D ω)) ≤ 0 :=
      le_trans (measure_mono hsub) (le_of_eq hUnion)
    exact le_antisymm hle (by exact zero_le)
  exact setLIntegral_measure_zero _ _ hPay