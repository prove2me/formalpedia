-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:08:11.265011+00:00
-- url     : https://prove2.me/submissions/7a777a03-e445-45e9-bb6b-3af2b980623c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- L1 of the genuine strict pre-ruin cash at a bounded physical stop. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hσbound : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) P := by
  classical
  have hσmeas : Measurable (fun ω : Ω => (σ ω : ℝ)) :=
    avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable σ hσstop
  have hRuinM : Measurable (ruinTime X x D) :=
    (ruinTime_stopping_rightCont_filtration X x D hD.1.1).measurable'
  let E : Ω → Set ℝ := fun ω =>
    paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ)
  have hE (ω : Ω) : MeasurableSet (E ω) :=
    (paymentTimes_measurable (ruinTime X x D ω)).inter measurableSet_Iio
  let A : Set (ℝ × Ω) :=
    {p | p.1 ∈ paymentTimes (ruinTime X x D p.2) ∧ p.1 < (σ p.2 : ℝ)}
  have hA : MeasurableSet A :=
    (paymentTimes_joint_measurable (ruinTime X x D) hRuinM).inter
      (measurableSet_lt measurable_fst (hσmeas.comp measurable_snd))
  let W : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  have hW : Measurable W :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul measurable_id).neg))
  obtain ⟨κ, hκs, hκ⟩ :=
    dividendMeasure_global_sfinite_kernel_exists D hD.1.1
  letI : IsSFiniteKernel κ := hκs
  have hKernel := measurable_random_indicator_lintegral κ A hA W hW
  have hEq : (fun ω : Ω =>
      ∫⁻ t in E ω, W t ∂dividendMeasure D ω) =
      (fun ω : Ω => ∫⁻ t, if (t, ω) ∈ A then W t else 0 ∂κ ω) := by
    funext ω
    rw [hκ ω, ← lintegral_indicator (hE ω) W]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ E ω
    · have htA : (t, ω) ∈ A := ht
      simp [Set.indicator, ht, htA]
    · have htA : (t, ω) ∉ A := fun hs => ht hs
      simp [Set.indicator, ht, htA]
  have hStrictENN : Measurable (fun ω : Ω =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) := by
    change Measurable (fun ω : Ω => ∫⁻ t in E ω, W t ∂dividendMeasure D ω)
    rw [hEq]
    simpa only [A, Set.mem_setOf_eq] using hKernel
  have hStrictMeas : AEStronglyMeasurable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) P :=
    (ENNReal.measurable_toReal.comp hStrictENN).aestronglyMeasurable
  have hClosedI : Integrable (fun ω : Ω =>
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal) P :=
    avram_wave6_08_original_bounded_random_clock_full_stieltjes_cash_integrable
      X x C D hD q σ T hσmeas hσbound
  have hStrictNN : ∀ᵐ ω ∂P,
      0 ≤ (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal := by
    filter_upwards [] with ω
    exact ENNReal.toReal_nonneg
  have hStrictLe : ∀ᵐ ω ∂P,
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal ≤
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal := by
    filter_upwards [] with ω
    have hSplit :=
      avram_p3_g2_original_closed_cash_eq_strict_plus_active_right_atom
        X x C D hD ω q hq (σ ω)
    by_cases hActive : σ ω = 0 ∨
        (σ ω : ℝ≥0∞) < ruinTime X x D ω
    · rw [if_pos hActive] at hSplit
      have hΔ : 0 ≤ rightLimit D (σ ω) ω - D (σ ω) ω :=
        sub_nonneg.mpr
          (dividendStrategy_le_rightLimit D hD.1.1 ω (σ ω))
      have he : 0 ≤ Real.exp (-(q * (σ ω : ℝ))) :=
        (Real.exp_pos _).le
      have hProd := mul_nonneg he hΔ
      linarith
    · rw [if_neg hActive] at hSplit
      simp only [add_zero] at hSplit
      exact le_of_eq hSplit.symm
  exact hClosedI.mono_nonneg hStrictMeas hStrictNN hStrictLe
