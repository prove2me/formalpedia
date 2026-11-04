-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_c_bvchain_original_discounted_strict_pre_cell_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:05:58.320202+00:00
-- url     : https://prove2.me/submissions/bb0f1ebe-b77b-42fe-96e1-418caafbe052

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_original_pre_rightpayment_strict_cell_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_p3_c_bvchain_public_discount_left_full_measure_le
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
import Theorems.Thm_AvramDividend_Classical_paymentTimes_Ioc_subset_of_terminal_survival
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Once-discounted strict-open dividend cell, genuine prepayment endpoint. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ, V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (a b : ℝ≥0) (hab : a < b)
    (hPre : (b : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Ioo (a : ℝ) (b : ℝ), ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      Real.exp (-(q * (a : ℝ))) * (V (x + X.X b ω - D b ω) - V (x + X.X b ω - rightLimit D a ω)) ≤ 0 := by
  have hStrategy : IsDividendStrategy 𝓕 D := hD.1.1
  let μ := dividendMeasure D ω
  let A : Set ℝ := Ioo (a : ℝ) (b : ℝ)
  let B : Set ℝ := Ioc (a : ℝ) (b : ℝ)
  let L : Set ℝ := Iio (b : ℝ)
  have hSets : B ∩ L = A := by
    ext t
    simp only [mem_inter_iff, mem_Ioc, mem_Iio, mem_Ioo]
    constructor
    · intro ht
      exact ⟨ht.1.1, ht.2⟩
    · intro ht
      exact ⟨⟨ht.1, ht.2.le⟩, ht.2⟩
  have hIncClosed : Ioc (a : ℝ) (b : ℝ) ⊆ paymentTimes (ruinTime X x D ω) := by
    apply paymentTimes_Ioc_subset_of_terminal_survival
    · exact a.property
    · simpa using hPre
  have hInclude : A ⊆ paymentTimes (ruinTime X x D ω) := by
    intro t ht
    exact hIncClosed ⟨ht.1, ht.2.le⟩
  have hSet : paymentTimes (ruinTime X x D ω) ∩ A = A := by
    ext t
    constructor
    · exact fun ht => ht.2
    · exact fun ht => ⟨hInclude ht, ht⟩
  have hRestr : (μ.restrict L) B = μ A := by
    rw [Measure.restrict_apply measurableSet_Ioc, hSets]
  have hFinite : ENNReal.ofReal (Real.exp (-(q * (a : ℝ)))) * (μ.restrict L) B ≠ ⊤ := by
    rw [hRestr, show μ A = ENNReal.ofReal (D b ω - rightLimit D a ω) from
      avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit D hStrategy ω a b hab]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hCash := avram_p3_c_bvchain_public_discount_left_full_measure_le q hq (μ.restrict L) (a : ℝ) (b : ℝ)
  have hCashReal := ENNReal.toReal_mono hFinite hCash
  have hCashScaled : (∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ).toReal ≤
      Real.exp (-(q * (a : ℝ))) * (μ A).toReal := by
    have hL : (∫⁻ t in B, ENNReal.ofReal (Real.exp (-(q * t))) ∂(μ.restrict L)) =
      (∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) := by
      change (∫⁻ t, ENNReal.ofReal (Real.exp (-(q * t))) ∂((μ.restrict L).restrict B)) =
        (∫⁻ t, ENNReal.ofReal (Real.exp (-(q * t))) ∂(μ.restrict A))
      rw [Measure.restrict_restrict measurableSet_Ioc, hSets]
    rw [hL, hRestr] at hCashReal
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hCashReal
  have hDrop := avram_p3_c_bvchain_original_pre_rightpayment_strict_cell_nonpos
    X x C hC w V hw_cont hw_smooth hw_grad hVtop hVfinite D hD ω a b hab hPre
  have hWeighted := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-(q * (a : ℝ)))).le hDrop
  dsimp only [μ, A] at *
  rw [hSet]
  nlinarith only [hCashScaled, hWeighted]
