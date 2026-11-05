-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_p4f_masked_preruin_signed_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:31:37.177858+00:00
-- url     : https://prove2.me/submissions/1007661d-da24-4877-83f1-1d41fe348a97

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_P4F_pre_ruin_hW_full_cash_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Cash : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (s : Set Ω)
    (hs : s = {ω | τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω})
    (hsMeas : MeasurableSet s)
    (hCashI : Integrable Cash P)
    (hAfterI : Integrable (fun ω => V (W ω)) P)
    (hBeforeI : Integrable
      (fun ω => V (x + X.X (τ ω) ω)) P) :
    let H : Ω → ℝ := s.indicator (fun ω =>
      Cash ω + V (W ω) - V (x + X.X (τ ω) ω))
    Integrable H P ∧ (∀ᵐ ω ∂P, H ω ≤ 0) := by
  classical
  dsimp
  constructor
  · exact ((hCashI.add hAfterI).sub hBeforeI).indicator hsMeas
  · filter_upwards [
      avram_p4_d_dividend_original_P4F_pre_ruin_hW_full_cash_nonpositive
        X x C q hq w V hw_cont hw_smooth hw_grad hVtop
        hVfinite D hD τ W Cash hW hCash
    ] with ω hω
    by_cases hωs : ω ∈ s
    · have hpre : τ ω = 0 ∨
          (τ ω : ℝ≥0∞) < ruinTime X x D ω := by
        simpa only [hs, mem_setOf_eq] using hωs
      simpa only [Set.indicator_of_mem hωs] using hω hpre
    · simp only [Set.indicator_of_notMem hωs]
      exact le_refl 0
