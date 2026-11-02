-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T20:22:22.825807+00:00
-- url     : https://prove2.me/submissions/8cb4dace-a9c2-4ad7-ae49-c680a0b520dd

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- One closed-horizon, full original Stieltjes cash budget at every cap,
including zero and infinity; all jump and singular-continuous mass remains. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X T ω - rightLimit D T ω) -
        V (x + X.X T ω)) ≤ 0 := by
  by_cases hCzero : C = 0
  · have hAdmissible : IsAdmissible X x D := hD.1
    have hStrategy : IsDividendStrategy 𝓕 D := hAdmissible.1
    have hPay := hAdmissible.2 ω T hPre
    have hCover : rightLimit D T ω ≤ x + X.X T ω := by
      dsimp [riskProcess] at hPay
      linarith only [hPay]
    have hDnonneg : 0 ≤ D T ω := by
      have hm := hStrategy.2.1 ω (show (0 : ℝ≥0) ≤ T from zero_le)
      simpa only [hStrategy.1 ω] using hm
    have hRnonneg : 0 ≤ rightLimit D T ω :=
      le_trans hDnonneg (dividendStrategy_le_rightLimit D hStrategy ω T)
    have hAfter : 0 ≤ x + X.X T ω - rightLimit D T ω := by
      linarith only [hCover]
    have hBefore : 0 ≤ x + X.X T ω := by
      linarith only [hAfter, hRnonneg]
    have hVzero : ∀ y : ℝ,
        V y = if y ≤ 0 then w y else w 0 + y := by
      intro y
      have hForm := hVfinite (by simp [hCzero]) y
      simpa only [hCzero, ENNReal.toReal_zero, sub_zero] using hForm
    have hVaffine : ∀ y : ℝ, 0 ≤ y → V y = w 0 + y := by
      intro y hy
      rw [hVzero y]
      split_ifs with hz
      · have heq : y = 0 := le_antisymm hz hy
        subst y
        ring
      · rfl
    have hDrop : V (x + X.X T ω) -
        V (x + X.X T ω - rightLimit D T ω) =
          rightLimit D T ω := by
      rw [hVaffine _ hBefore, hVaffine _ hAfter]
      ring
    have hBudget := avram_wave3_03_bv_discounted_closed_horizon_stieltjes_bound
      q hq D hStrategy ω T
    have hReal := ENNReal.toReal_mono (by simp) hBudget
    rw [ENNReal.toReal_ofReal hRnonneg] at hReal
    linarith only [hReal, hDrop]
  · have hCpos : 0 < C := pos_iff_ne_zero.mpr hCzero
    exact avram_wave5_04b_positive_cap_original_global_closed_horizon_real_signed_nonpos
      X x C hCpos q hq w V hw_cont hw_smooth hw_grad
      hVtop hVfinite D hD ω T hPre
