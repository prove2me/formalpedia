-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_positive_clock_budget_to_signed_source
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T12:18:19.334796+00:00
-- url     : https://prove2.me/submissions/9aa18a24-cbb3-4f1d-8829-a4702dc8bad4

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_allcap_ennreal_bound_to_signed_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (τ : Ω → ℝ≥0) (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hZeroMeas : MeasurableSet {ω | τ ω = 0})
    (hwx : 0 ≤ w x)
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hTermPos : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hCashPos : ∀ᵐ ω ∂P, 0 ≤ Cash ω)
    (hPositive : (∫⁻ ω in {ω | τ ω ≠ 0},
        ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x) * P {ω | τ ω ≠ 0}) :
    ∃ M G H : Ω → ℝ,
      Integrable M P ∧ Integrable G P ∧ Integrable H P ∧
      (∫ ω, M ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  let s : Set Ω := {ω | τ ω = 0}
  have hs : MeasurableSet s := hZeroMeas
  have hzero : (∫⁻ ω in s, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x) * P s := by
    calc
      (∫⁻ ω in s, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
          (∫⁻ ω in s, ENNReal.ofReal (w x) ∂P) := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hs] with ω hω
        exact ENNReal.ofReal_le_ofReal
          (avram_ubv_hor3_original_zero_clock_term_cash_pathwise_le
            X x q w C D hD hjump τ W Cash Term hW hCash hTerm ω hω)
      _ = ENNReal.ofReal (w x) * P s :=
        setLIntegral_const s (ENNReal.ofReal (w x))
  have hpos : (∫⁻ ω in sᶜ, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x) * P sᶜ := by
    change (∫⁻ ω in {ω | τ ω ≠ 0}, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x) * P {ω | τ ω ≠ 0}
    exact hPositive
  have hExpected : (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
    calc
      (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) =
          (∫⁻ ω in s, ENNReal.ofReal (Term ω + Cash ω) ∂P) +
          (∫⁻ ω in sᶜ, ENNReal.ofReal (Term ω + Cash ω) ∂P) := by
        exact (lintegral_add_compl
          (fun ω => ENNReal.ofReal (Term ω + Cash ω)) hs).symm
      _ ≤ ENNReal.ofReal (w x) * P s +
          ENNReal.ofReal (w x) * P sᶜ := add_le_add hzero hpos
      _ = ENNReal.ofReal (w x) * (P s + P sᶜ) := (mul_add ..).symm
      _ = ENNReal.ofReal (w x) := by
        rw [measure_add_measure_compl hs]
        simp
  exact avram_p4_f3_allcap_ennreal_bound_to_signed_source
    X w x hwx Term Cash hTermMeas hCashI hTermPos hCashPos hExpected

