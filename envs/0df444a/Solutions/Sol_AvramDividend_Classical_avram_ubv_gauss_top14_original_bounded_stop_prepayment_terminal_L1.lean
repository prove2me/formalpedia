-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gauss_top14_original_bounded_stop_prepayment_terminal_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T07:57:03.809174+00:00
-- url     : https://prove2.me/submissions/03ca77d6-9055-4e31-bf42-104913189f55

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top9_original_topcap_w_nonnegative_everywhere
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
import Theorems.Thm_AvramDividend_Classical_avram_p3_g2_original_prepayment_riskProcess_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04b_cap_extension_measurable_of_zero_negative
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_path_nonneg

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original positive-Gaussian top-cap prepayment terminal is L1 at
    bounded true stopping clocks; no right dividend is deducted at the clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hσbound : ∀ ω, σ ω ≤ T) :
    Integrable (fun ω => Real.exp (-(q * (σ ω : ℝ))) *
      w (riskProcess X x D (σ ω) ω)) P := by
  obtain ⟨θ, K, hθ, hK, hwGrowth⟩ :=
    avram_p4_f4_turn16_gaussian_HJB_global_exponential_growth
      X hX hBV hν q hq w C hC hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad hTop
  have hσENN : Measurable (fun ω : Ω => (σ ω : WithTop ℝ≥0)) :=
    hσstop.measurable'
  have hσNN : Measurable σ :=
    measurable_coe_nnreal_ennreal_iff.mp hσENN
  have hσReal : Measurable (fun ω : Ω => (σ ω : ℝ)) :=
    hσNN.coe_nnreal_real
  have hwMeas : Measurable w :=
    avram_wave6_04b_cap_extension_measurable_of_zero_negative
      w w C hw_cont hw_neg
      (by intro _ y; rfl)
      (by intro hn; exact (hn hTop).elim)
  have hRiskMeas : Measurable
      (fun ω => riskProcess X x D (σ ω) ω) := by
    have hjoint :=
      avram_p3_g2_original_prepayment_riskProcess_joint_measurable
        X x D hD.1.1
    exact hjoint.comp (hσNN.prodMk measurable_id)
  have hTermMeas : AEStronglyMeasurable
      (fun ω => Real.exp (-(q * (σ ω : ℝ))) *
        w (riskProcess X x D (σ ω) ω)) P := by
    have hdisc : Measurable (fun ω => Real.exp (-(q * (σ ω : ℝ)))) :=
      (measurable_const.mul hσReal).neg.exp
    exact (hdisc.mul (hwMeas.comp hRiskMeas)).aestronglyMeasurable
  have hwNonneg := avram_ubv_top9_original_topcap_w_nonnegative_everywhere
    w C hTop hw0 hw_cont hw_neg hw_smooth hw_grad
  have hTermNonneg : ∀ᵐ ω ∂P,
      0 ≤ Real.exp (-(q * (σ ω : ℝ))) *
        w (riskProcess X x D (σ ω) ω) :=
    Filter.Eventually.of_forall (fun ω =>
      mul_nonneg (le_of_lt (Real.exp_pos _)) (hwNonneg _))
  have hRiskLe (ω : Ω) :
      riskProcess X x D (σ ω) ω ≤ x + X.X (σ ω) ω := by
    have hD0 : 0 ≤ D (σ ω) ω :=
      dividendStrategy_path_nonneg D hD.1.1 ω (σ ω)
    dsimp [riskProcess]
    linarith
  have hUpper (ω : Ω) :
      Real.exp (-(q * (σ ω : ℝ))) *
        w (riskProcess X x D (σ ω) ω) ≤
      Real.exp (-(q * (σ ω : ℝ))) *
        (K * Real.exp (θ * (x + X.X (σ ω) ω))) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt (Real.exp_pos _))
    calc
      w (riskProcess X x D (σ ω) ω) ≤
          K * Real.exp (θ * riskProcess X x D (σ ω) ω) :=
        hwGrowth _
      _ ≤ K * Real.exp (θ * (x + X.X (σ ω) ω)) := by
        apply mul_le_mul_of_nonneg_left _ hK
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hRiskLe ω) hθ)
  have hSrc : Integrable (fun ω => Real.exp
      (θ * X.X (σ ω) ω - (σ ω : ℝ) * q)) P :=
    avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
      X θ hθ q σ hσReal hσstop T hσbound
  have hRawEq : (fun ω => Real.exp (-(q * (σ ω : ℝ))) *
        (K * Real.exp (θ * (x + X.X (σ ω) ω)))) =
      (fun ω => (K * Real.exp (θ * x)) *
        Real.exp (θ * X.X (σ ω) ω - (σ ω : ℝ) * q)) := by
    funext ω
    have hExp : Real.exp (-(q * (σ ω : ℝ))) *
        Real.exp (θ * (x + X.X (σ ω) ω)) =
        Real.exp (θ * x) *
          Real.exp (θ * X.X (σ ω) ω - (σ ω : ℝ) * q) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    calc
      Real.exp (-(q * (σ ω : ℝ))) *
          (K * Real.exp (θ * (x + X.X (σ ω) ω))) =
        K * (Real.exp (-(q * (σ ω : ℝ))) *
          Real.exp (θ * (x + X.X (σ ω) ω))) := by ring
      _ = K * (Real.exp (θ * x) *
          Real.exp (θ * X.X (σ ω) ω - (σ ω : ℝ) * q)) := by rw [hExp]
      _ = (K * Real.exp (θ * x)) *
          Real.exp (θ * X.X (σ ω) ω - (σ ω : ℝ) * q) := by ring
  have hRawI : Integrable (fun ω =>
      Real.exp (-(q * (σ ω : ℝ))) *
        (K * Real.exp (θ * (x + X.X (σ ω) ω)))) P := by
    rw [hRawEq]
    exact hSrc.const_mul _
  exact hRawI.mono_nonneg hTermMeas hTermNonneg
    (Filter.Eventually.of_forall hUpper)
