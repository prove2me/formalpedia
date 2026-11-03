-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_03_original_bounded_measurable_random_clock_signed_stieltjes_integrable_unconditionally
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:30:32.330082+00:00
-- url     : https://prove2.me/submissions/a4464887-2a8b-487c-841a-8f0f61a51073

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- Direct source-measure argument for P-integrability of the original
    discounted signed Stieltjes payout at any bounded measurable clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q)
    (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτBound : ∀ ω, τ ω ≤ T)
    (hτMeas : Measurable (fun ω => (τ ω : ℝ))) :
    Integrable (fun ω : Ω =>
      ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P := by
  let F : Ω → ℝ≥0∞ := fun ω =>
    ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)
  let g : Ω → ℝ := fun ω =>
    ∫ t in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      Real.exp (-(q * t)) ∂(dividendMeasure D ω)
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hMeanEq :=
    avram_wave7_03_original_full_ruin_bounded_clock_unconditional_mean_eq
      X x C D hD q hq T τ hτBound hτMeas
  have hCashFinite : (∫⁻ ω, F ω ∂P) < ⊤ := by
    change (∫⁻ ω, F ω ∂P) =
      ENNReal.ofReal (∫ ω, g ω ∂P) at hMeanEq
    rw [hMeanEq]
    exact ENNReal.ofReal_lt_top
  have hFm : Measurable F :=
    avram_wave6_06_original_random_upper_clock_complete_stieltjes_cash_measurable
      X x D hDiv q (fun ω => (τ ω : ℝ)) hτMeas
  have hFInt : Integrable (fun ω => (F ω).toReal) P :=
    MeasureTheory.integrable_toReal_of_lintegral_ne_top
      hFm.aemeasurable (ne_of_lt hCashFinite)
  have hPath (ω : Ω) : F ω = ENNReal.ofReal (g ω) :=
    avram_wave7_03_original_real_horizon_pathwise_full_stieltjes_eq
      X x D hDiv ω (τ ω : ℝ) (NNReal.coe_nonneg _) q hq
  have hg (ω : Ω) : 0 ≤ g ω := by
    apply integral_nonneg
    intro t
    exact (Real.exp_pos (-(q * t))).le
  have hEq : (fun ω => (F ω).toReal) =ᵐ[P] g := by
    apply Filter.Eventually.of_forall
    intro ω
    calc
      (F ω).toReal = (ENNReal.ofReal (g ω)).toReal :=
        congrArg ENNReal.toReal (hPath ω)
      _ = g ω := ENNReal.toReal_ofReal (hg ω)
  exact hFInt.congr hEq
