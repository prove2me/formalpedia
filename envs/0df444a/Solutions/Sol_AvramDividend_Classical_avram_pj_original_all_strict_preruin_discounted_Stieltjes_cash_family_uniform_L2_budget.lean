-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_all_strict_preruin_discounted_Stieltjes_cash_family_uniform_L2_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:34:18.97633+00:00
-- url     : https://prove2.me/submissions/031a24c1-1be0-4932-8849-0c9885af5de2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_true_preruin_full_discounted_Stieltjes_cash_square_integrable_from_runningSup
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_real_stopped_cash_le_original_total_mass
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_dividend_rightLimit_nonnegative
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_all_UBV_true_fixedhorizon_runningSup_L1
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_unboundedvariation_finitehorizon_runningSup_square_integrable
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- All strictly pre-ruin original discounted dividend cash physical
clocks share the same finite genuine Levy running-supremum L2 budget. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (n : ℝ≥0) (ρ : ℕ → Ω → ℝ≥0)
    (hρle : ∀ k ω, ρ k ω ≤ n)
    (hρpre : ∀ k ω, (ρ k ω : ℝ≥0∞) <
      ruinTime X x D ω)
    (Cash : ℕ → Ω → ℝ)
    (hCash : ∀ k ω, Cash k ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Iic (ρ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashMeas : ∀ k, Measurable (Cash k)) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ k, Integrable (fun ω => (Cash k ω)^2) P ∧
        (∫ ω, (Cash k ω)^2 ∂P) ≤ B := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hSupI :=
    avram_f6_original_all_UBV_true_fixedhorizon_runningSup_L1 X hBV n
  have hSup2 :=
    avram_pj_original_unboundedvariation_finitehorizon_runningSup_square_integrable
      X hBV n
  have hDomI : Integrable (fun ω =>
      (x + runningSup X n ω)^2) P := by
    have ha : Integrable (fun ω =>
        x^2 + 2*x*runningSup X n ω +
          (runningSup X n ω)^2) P :=
      ((integrable_const (x^2)).add (hSupI.const_mul (2*x))).add hSup2
    convert ha using 1
    funext ω
    ring
  refine ⟨∫ ω, (x + runningSup X n ω)^2 ∂P,
    integral_nonneg (fun ω => sq_nonneg _), ?_⟩
  intro k
  have hSqI :=
    avram_pj_original_true_preruin_full_discounted_Stieltjes_cash_square_integrable_from_runningSup
      X hBV x D hD q hq n (ρ k)
      (hρle k) (hρpre k) (Cash k)
      (hCash k) (hCashMeas k)
  refine ⟨hSqI, ?_⟩
  apply integral_mono_ae hSqI hDomI
  filter_upwards [] with ω
  obtain ⟨h0,hUpper⟩ :=
    avram_p4_d_dividend_original_real_stopped_cash_le_original_total_mass
      D hD ω (ruinTime X x D ω) (ρ k ω) q hq
      (Cash k ω) (hCash k ω)
  have hDnonneg :=
    avram_ga_a35_original_dividend_rightLimit_nonnegative
      D hD (ρ k ω) ω
  have hDcash : Cash k ω ≤ rightLimit D (ρ k ω) ω := by
    simpa only [ENNReal.toReal_ofReal hDnonneg] using hUpper
  have hPreruin :=
    avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
      X x D hD (ρ k ω) ω (hρpre k ω)
  have hSupMono : runningSup X (ρ k ω) ω ≤ runningSup X n ω :=
    (runningSup_monotone_and_path_le X ω).1 (hρle k ω)
  have hBound : Cash k ω ≤ x + runningSup X n ω := by linarith
  have hDomNonneg : 0 ≤ x + runningSup X n ω := le_trans h0 hBound
  nlinarith [mul_nonneg (sub_nonneg.mpr hBound)
    (add_nonneg hDomNonneg h0)]
