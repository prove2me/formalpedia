-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_cash_prefix_positive_F_and_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:00:56.548391+00:00
-- url     : https://prove2.me/submissions/a6aff703-feae-487b-8c30-579aeb4aeebb

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_prebudget_L1
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_cash_terminal_fatou_liminf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original BV strict cash-prefix grid with its unchanged surviving
pre-right-payment terminal supplies all source-dependent positive-payoff
and Fatou requirements. No signed source budget is postulated here. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδle : ∀ n, δ n ≤ T)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let F : ℕ → Ω → ℝ := fun n ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
       else 0)
    (∀ n, Measurable (F n) ∧ Integrable (F n) P ∧
      (∀ ω, 0 ≤ F n ω)) ∧
    (∀ ω, ENNReal.ofReal
      ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       (if (S : ℝ≥0∞) < ruinTime X x D ω then
          Real.exp (-(q * T)) * w (riskProcess X x D S ω)
        else 0)) ≤
      liminf (fun n => ENNReal.ofReal (F n ω)) atTop) := by
  intro S F
  let term : Ω → ℝ := fun ω =>
    if (S : ℝ≥0∞) < ruinTime X x D ω then
      Real.exp (-(q * T)) * w (riskProcess X x D S ω) else 0
  let cash : ℕ → Ω → ℝ := fun n ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  let full : Ω → ℝ := fun ω =>
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  have hDiv : IsDividendStrategy 𝓕 D := hD.1.1
  have hSpos : 0 < S := by exact_mod_cast hT
  have hTermNonneg (ω : Ω) : 0 ≤ term ω := by
    dsimp [term]
    split_ifs with hSurv
    · exact mul_nonneg (Real.exp_pos _).le (hw_nonneg ω S hSpos hSurv)
    · exact le_refl _
  have hTermMeas : Measurable term := by
    have hPair : Measurable (fun ω : Ω => (S, ω)) :=
      measurable_const.prodMk measurable_id
    have hRisk : Measurable (fun ω : Ω =>
        riskProcess X x D S ω) := by
      simpa only [Function.comp_def] using
        (avram_p3_g2_original_prepayment_riskProcess_joint_measurable
          X x D hDiv).comp hPair
    have hwMeas : Measurable w :=
      (local_verification_candidate_borel_and_postPayment_adapted
        X x D hDiv w hw_cont hw_neg).1
    have hSurv : MeasurableSet
        {ω : Ω | (S : ℝ≥0∞) < ruinTime X x D ω} :=
      measurableSet_lt measurable_const
        (ruinTime_measurable X x D hDiv)
    change Measurable (fun ω : Ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0)
    exact Measurable.ite hSurv
      (measurable_const.mul (hwMeas.comp hRisk)) measurable_const
  have hCashMeas (n : ℕ) : Measurable (cash n) := by
    exact (avram_p3_bv_original_strict_cash_measurable
      D hDiv (ruinTime X x D) (ruinTime_measurable X x D hDiv)
      q (T - δ n)).ennreal_toReal
  have hCashInt (n : ℕ) : Integrable (cash n) P := by
    exact avram_p3_bv_original_strict_cash_L1
      X x C D hD q hq (T - δ n) (sub_nonneg.mpr (hδle n))
  have hFullInt : Integrable full P := by
    exact avram_p3_bv_original_strict_cash_L1
      X x C D hD q hq T hT.le
  have hTotalInt : Integrable (fun ω : Ω => full ω + term ω) P := by
    simpa only [full, term, S] using
      (avram_p3_bv_original_prebudget_L1
        X hBV x C D hD w hw_cont hw_neg q hq T hT.le)
  have hTermInt : Integrable term P := by
    have hDiff : Integrable
        (fun ω : Ω => (full ω + term ω) - full ω) P :=
      hTotalInt.sub hFullInt
    have hEq : (fun ω : Ω => (full ω + term ω) - full ω) = term := by
      funext ω
      ring
    rw [hEq] at hDiff
    exact hDiff
  constructor
  · intro n
    refine ⟨?_, ?_, ?_⟩
    · change Measurable (fun ω : Ω => cash n ω + term ω)
      exact (hCashMeas n).add hTermMeas
    · change Integrable (fun ω : Ω => cash n ω + term ω) P
      exact (hCashInt n).add hTermInt
    · intro ω
      change 0 ≤ cash n ω + term ω
      exact add_nonneg ENNReal.toReal_nonneg (hTermNonneg ω)
  · intro ω
    simpa only [S, F, cash, term] using
      (avram_p3_grid4_original_strict_cash_terminal_fatou_liminf
        X x C D hD ω w q hq T hT δ hδpos hδanti hδ)
