-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_true_preruin_full_discounted_Stieltjes_cash_square_integrable_from_runningSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:11:06.831631+00:00
-- url     : https://prove2.me/submissions/8d5f6679-5d15-449c-a99c-4d035084cbe4

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_unboundedvariation_finitehorizon_runningSup_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_all_UBV_true_fixedhorizon_runningSup_L1
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_real_stopped_cash_le_original_total_mass
import Theorems.Thm_AvramDividend_Classical_avram_ga_a35_original_dividend_rightLimit_nonnegative
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Square-integrable original ruin-clipped Stieltjes dividend cash on a
strictly surviving random physical clock.  The dominator is the genuine
initial reserve plus the original finite-horizon running supremum. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (n : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρle : ∀ ω, ρ ω ≤ n)
    (hρpre : ∀ ω, (ρ ω : ℝ≥0∞) <
      ruinTime X x D ω)
    (Cash : Ω → ℝ)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashMeas : Measurable Cash) :
    Integrable (fun ω => (Cash ω)^2) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hSupI :=
    avram_f6_original_all_UBV_true_fixedhorizon_runningSup_L1
      X hBV n
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
  have hBound (ω : Ω) :
      0 ≤ Cash ω ∧ Cash ω ≤ x + runningSup X n ω := by
    obtain ⟨h0, hDupper⟩ :=
      avram_p4_d_dividend_original_real_stopped_cash_le_original_total_mass
        D hD ω (ruinTime X x D ω) (ρ ω) q hq
        (Cash ω) (hCash ω)
    have hDnonneg :=
      avram_ga_a35_original_dividend_rightLimit_nonnegative
        D hD (ρ ω) ω
    have hDcash : Cash ω ≤ rightLimit D (ρ ω) ω := by
      simpa only [ENNReal.toReal_ofReal hDnonneg] using hDupper
    have hPreruin :=
      avram_pj_original_strict_preruin_right_dividends_le_initial_plus_true_Levy_runningSup
        X x D hD (ρ ω) ω (hρpre ω)
    have hSupMono : runningSup X (ρ ω) ω ≤ runningSup X n ω :=
      (runningSup_monotone_and_path_le X ω).1 (hρle ω)
    exact ⟨h0, by linarith⟩
  have hSq : ∀ ω, (Cash ω)^2 ≤
      (x + runningSup X n ω)^2 := by
    intro ω
    obtain ⟨ha, hb⟩ := hBound ω
    have hc : 0 ≤ x + runningSup X n ω := le_trans ha hb
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (add_nonneg hc ha)]
  apply Integrable.mono' hDomI
    ((hCashMeas.pow_const 2).aestronglyMeasurable)
  filter_upwards [] with ω
  have h0 : 0 ≤ (Cash ω)^2 := sq_nonneg _
  have h1 : 0 ≤ (x + runningSup X n ω)^2 := sq_nonneg _
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg h0, abs_of_nonneg h1] using hSq ω
