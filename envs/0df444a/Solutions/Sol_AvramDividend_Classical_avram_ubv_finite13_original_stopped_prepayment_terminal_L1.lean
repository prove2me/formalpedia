-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite13_original_stopped_prepayment_terminal_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:36:45.700956+00:00
-- url     : https://prove2.me/submissions/ab965c6d-e76a-4fb4-aff4-d9215fcfe390

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_finitecap_continuous_payoff_uniform_bound
import Theorems.Thm_AvramDividend_Classical_admissibleLe_riskProcess_le_cap_all_times
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A finite-cap original prepayment value has a uniform discounted L¹ bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q) (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    Integrable (fun ω =>
      Real.exp (-(q * (σ ω : ℝ))) *
        w (riskProcess X x D (σ ω) ω)) P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  have hσNN : Measurable σ :=
    measurable_coe_nnreal_ennreal_iff.mp hσstop.measurable'
  have hσReal : Measurable (fun ω : Ω => (σ ω : ℝ)) :=
    hσNN.coe_nnreal_real
  have hPair : Measurable (fun ω : Ω => (σ ω, ω)) :=
    hσNN.prodMk measurable_id
  have hRisk : Measurable (fun ω : Ω => riskProcess X x D (σ ω) ω) := by
    simpa only [Function.comp_def] using
      (avram_p3_g2_original_prepayment_riskProcess_joint_measurable
        X x D hD.1.1).comp hPair
  have hwMeas : Measurable w :=
    avram_wave6_04b_cap_extension_measurable_of_zero_negative
      w w (⊤ : ℝ≥0∞) hw_cont hw_neg
      (by intro _ y; rfl) (by intro h; exact (h rfl).elim)
  have hExpMeas : Measurable (fun ω : Ω =>
      Real.exp (-(q * (σ ω : ℝ)))) :=
    Real.continuous_exp.measurable.comp
      ((measurable_const.mul hσReal).neg)
  have hTermMeas : AEStronglyMeasurable (fun ω : Ω =>
      Real.exp (-(q * (σ ω : ℝ))) * w (riskProcess X x D (σ ω) ω)) P :=
    (hExpMeas.mul (hwMeas.comp hRisk)).aestronglyMeasurable
  obtain ⟨B, hB, hPayBound⟩ :=
    avram_p4_e_localise_finitecap_continuous_payoff_uniform_bound
      w hw_cont C.toReal ENNReal.toReal_nonneg
  have hRiskBound (ω : Ω) : |w (riskProcess X x D (σ ω) ω)| ≤ B := by
    by_cases hy : 0 ≤ riskProcess X x D (σ ω) ω
    · apply hPayBound _ hy
      have hcap := admissibleLe_riskProcess_le_cap_all_times
        X x C D hD hxc ω (σ ω)
      simpa only [ENNReal.ofReal_toReal hfinite] using hcap
    · have hneg : riskProcess X x D (σ ω) ω < 0 := lt_of_not_ge hy
      simp [hw_neg _ hneg, hB]
  have hTermBound : ∀ ω : Ω,
      ‖Real.exp (-(q * (σ ω : ℝ))) *
        w (riskProcess X x D (σ ω) ω)‖ ≤ B := by
    intro ω
    have ht : 0 ≤ (σ ω : ℝ) := (σ ω).property
    have hp : 0 ≤ q * (σ ω : ℝ) := mul_nonneg hq ht
    have he : 0 ≤ Real.exp (-(q * (σ ω : ℝ))) := Real.exp_nonneg _
    have he1 : Real.exp (-(q * (σ ω : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      linarith
    calc
      ‖Real.exp (-(q * (σ ω : ℝ))) *
          w (riskProcess X x D (σ ω) ω)‖ =
          Real.exp (-(q * (σ ω : ℝ))) *
            |w (riskProcess X x D (σ ω) ω)| := by
              rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg he]
      _ ≤ |w (riskProcess X x D (σ ω) ω)| := by
          nlinarith [abs_nonneg (w (riskProcess X x D (σ ω) ω))]
      _ ≤ B := hRiskBound ω
  exact MeasureTheory.Integrable.of_bound hTermMeas B
    (Filter.Eventually.of_forall hTermBound)
