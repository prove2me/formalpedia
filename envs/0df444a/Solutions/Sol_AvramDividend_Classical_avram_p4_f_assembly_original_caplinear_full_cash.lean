-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_caplinear_full_cash
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T10:55:47.566184+00:00
-- url     : https://prove2.me/submissions/8734e528-9062-4009-8941-045d98b28b0d

import Mathlib.Probability.Process.Filtration
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
    (x : ℝ) (C : ℝ≥0∞) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Cash : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
        if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    ∀ᵐ ω ∂P, (τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) →
      Cash ω + V (W ω) - V (x + X.X (τ ω) ω) ≤ 0 := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  change ∀ᵐ ω ∂P, (τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω) →
    Cash ω + V (W ω) - V (x + X.X (τ ω) ω) ≤ 0
  have hVtop : C = ⊤ → ∀ z : ℝ, V z = w z := by
    intro hc z
    simp [V, hc]
  have hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal) := by
    intro hc z
    simp [V, hc]
  have hw_one : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} :=
    hw_smooth.of_le (by norm_num)
  exact avram_p4_d_dividend_original_P4F_pre_ruin_hW_full_cash_nonpositive
    X x C q (le_of_lt hq) w V hw_cont hw_one hw_grad
    hVtop hVfinite D hD τ W Cash hW hCash
