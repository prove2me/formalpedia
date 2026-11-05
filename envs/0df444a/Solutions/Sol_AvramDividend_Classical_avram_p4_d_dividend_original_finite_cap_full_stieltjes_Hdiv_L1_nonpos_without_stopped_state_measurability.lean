-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_finite_cap_full_stieltjes_Hdiv_L1_nonpos_without_stopped_state_measurability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T01:03:17.089147+00:00
-- url     : https://prove2.me/submissions/49770b09-1f5a-46af-aad9-0da41e284cfe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_ennreal_finite_cap_stopped_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_without_stopped_state_measurability
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_finite_cap_linear_extension_exponential_envelope_exists
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_preruin_branch_measurable_from_clock
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_piecewise_postpayment_caplinear_L1_from_discounted_Term
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_stopped_branch_L1_ae_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine original, closed-Stieltjes finite-cap dividend remainder is
L1 and a.e. nonpositive from P4-F's terminal AE measurability, with neither
an extra clock bound nor a full stopped-X measurability hypothesis. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCfin : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (q : ℝ) (hq : 0 ≤ q) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (hVtop : C = ⊤ → ∀ z : ℝ, V z = w z)
    (hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z else
        w C.toReal + (z - C.toReal))
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω : Ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term Hdiv : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨
      (τ ω : ℝ≥0∞) < ruinTime X x D ω then
      x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashI : Integrable Cash P)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hHdiv : ∀ ω, Hdiv ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        Cash ω + (V (W ω) - V (x + X.X (τ ω) ω))
      else 0) :
    Integrable Hdiv P ∧ ∀ᵐ ω ∂P, Hdiv ω ≤ 0 := by
  have hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0) :=
    avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_le_finite_horizon
      X x D n τ hτeq
  have hTermI : Integrable Term P :=
    avram_p4_f_assembly_original_ennreal_finite_cap_stopped_terminal_integrable
      X q hq w C hCfin hw_cont hw_neg x hxc D hD
      τ W Term hW hTerm hTermMeas
  obtain ⟨K, hK, hEnvelope⟩ :=
    avram_p4_d_dividend_original_finite_cap_linear_extension_exponential_envelope_exists
      C hCfin w V hw_cont hw_neg hVfinite
  have hVmeas : Measurable V :=
    avram_wave6_04b_cap_extension_measurable_of_zero_negative
      w V C hw_cont hw_neg hVtop hVfinite
  have hPre :=
    avram_p4_d_dividend_original_stopped_preruin_branch_measurable_from_clock
      X x C D hD τ hτmeas
  have hAfter :=
    avram_p4_d_dividend_original_piecewise_postpayment_caplinear_L1_from_discounted_Term
      X x C hC hxc q hq w V hVtop hVfinite D hD τ (n : ℝ≥0)
      hτbound hτmeas W Term hW hTerm hTermI
  have hBefore :=
    avram_p4_d_dividend_original_ruin_truncated_raw_caplinear_value_L1_without_stopped_state_measurability
      X x D n τ hτeq hτmeas hτstop V hVmeas K hK hEnvelope
  exact avram_p4_d_dividend_original_stopped_branch_L1_ae_nonpos
    X x C q hq w V hw_cont hw_smooth hw_grad hVtop hVfinite
    D hD τ W Cash Hdiv hW hCash hPre hCashI hAfter hBefore hHdiv
