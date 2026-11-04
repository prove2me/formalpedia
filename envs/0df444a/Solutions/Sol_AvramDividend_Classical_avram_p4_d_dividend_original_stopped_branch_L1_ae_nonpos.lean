-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_stopped_branch_L1_ae_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:00:31.663056+00:00
-- url     : https://prove2.me/submissions/687f540c-fff0-4488-9f05-1c46881875ff

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact source pre-ruin full Stieltjes remainder has an integrable,
nonpositive measurable branch under the corresponding true L¹ moments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q)
    (w V : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Cash Hdiv : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hPreMeas : MeasurableSet {ω : Ω |
      τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω})
    (hCashI : Integrable Cash P)
    (hVWI : Integrable (fun ω => V (W ω)) P)
    (hVSI : Integrable (fun ω => V (x + X.X (τ ω) ω)) P)
    (hHdiv : ∀ ω, Hdiv ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Cash ω + (V (W ω) - V (x + X.X (τ ω) ω))
      else 0) :
    Integrable Hdiv P ∧ ∀ᵐ ω ∂P, Hdiv ω ≤ 0 := by
  let A : Set Ω := {ω |
    τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω}
  have hA : MeasurableSet A := hPreMeas
  have hBaseI : Integrable
      (fun ω => Cash ω + (V (W ω) - V (x + X.X (τ ω) ω))) P :=
    hCashI.add (hVWI.sub hVSI)
  have hEq : Hdiv =
      A.indicator (fun ω => Cash ω +
        (V (W ω) - V (x + X.X (τ ω) ω))) := by
    funext ω
    by_cases h : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
    · simp [A, hHdiv ω, h]
    · simp [A, hHdiv ω, h]
  constructor
  · rw [hEq]
    exact hBaseI.indicator hA
  · filter_upwards [] with ω
    by_cases h : τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
    · rw [hHdiv ω, if_pos h]
      have hDomain :=
        avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
          X x D ω τ h
      have hBound :=
        avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
          X x C q hq w V hw_cont hw_smooth hw_grad
          hVtop hVfinite D hD ω (τ ω) h
      calc
        Cash ω + (V (W ω) - V (x + X.X (τ ω) ω)) =
            (∫⁻ s in Icc (0 : ℝ) (τ ω : ℝ),
              ENNReal.ofReal (Real.exp (-(q * s)))
                ∂(dividendMeasure D ω)).toReal +
              (V (x + X.X (τ ω) ω - rightLimit D (τ ω) ω) -
                V (x + X.X (τ ω) ω)) := by
                  rw [hCash ω, hDomain, hW ω, if_pos h]
        _ ≤ 0 := hBound
    · simp [hHdiv ω, h]