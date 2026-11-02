-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_actual_source_stopped_theta_scaled_fullStieltjes_cash_q_ge_psi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:38:35.300676+00:00
-- url     : https://prove2.me/submissions/33e7f48d-bcd8-4be4-a075-aa82e5ab8d63

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actualStopped_theta_exponential_payment_kernel_dominated
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_fullStieltjes_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical

/-- A general positive Laplace tilt gives original-source stopped expected
cash at any q≥ψ(θ), with the whole closed-horizon dividend measure. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (θ : ℝ) (hθ : 0 < θ) (q : ℝ) (hq : X.ψ θ ≤ q) (T : ℝ≥0) (hT : 0 < T) :
    ENNReal.ofReal θ * (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ), if s ∈ paymentTimes (ruinTime X x D ω) then ENNReal.ofReal (Real.exp (-(q * (s.toNNReal : ℝ)))) else 0 ∂dividendMeasure D ω ∂P) ≤
    ENNReal.ofReal (Real.exp (θ * x)) := by
  classical
  let a : ℝ≥0∞ := ENNReal.ofReal θ
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.exp (θ * x))
  let g : Ω → ℝ → ℝ≥0∞ := fun ω s => ENNReal.ofReal (Real.exp (θ * (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * X.ψ θ))
  have hgm (ω : Ω) : Measurable (g ω) := by
    have hjoint := avram_wave4_03_source_postPayment_discounted_exponential_joint_time_path_measurable X 0 D hD.1.1 θ (X.ψ θ)
    have htime : Measurable (fun s : ℝ => (s.toNNReal, ω)) := measurable_real_toNNReal.prodMk measurable_const
    have h := (hjoint.comp htime).ennreal_ofReal
    simpa only [g, Function.comp_def, zero_add] using h
  have hgo : Measurable (fun ω : Ω => ∫⁻ s in Icc (0 : ℝ) (T : ℝ), g ω s ∂dividendMeasure D ω) := by
    have hS : MeasurableSet {z : ℝ × Ω | z.1 ∈ Icc (0 : ℝ) (T : ℝ)} := measurableSet_Icc.preimage measurable_fst
    have h := avram_wave4_03_actual_source_exponential_random_fullStieltjes_lintegral_measurable X 0 D hD.1.1 θ (X.ψ θ) _ hS
    have h' : Measurable (fun ω : Ω => ∫⁻ s : ℝ, if s ∈ Icc (0 : ℝ) (T : ℝ) then g ω s else 0 ∂dividendMeasure D ω) := by
      simpa only [g, zero_add, Set.mem_setOf_eq] using h
    convert h' using 1
    funext ω
    rw [← lintegral_indicator measurableSet_Icc (g ω)]
    simp only [Set.indicator_apply]
  have hpoint (ω : Ω) (s : ℝ) : (if s ∈ paymentTimes (ruinTime X x D ω) then ENNReal.ofReal (Real.exp (-(q * (s.toNNReal : ℝ)))) else 0) ≤ c * g ω s := by
    by_cases hp : s ∈ paymentTimes (ruinTime X x D ω)
    · have hs : 0 ≤ s := (show 0 ≤ s ∧ (s = 0 ∨ ENNReal.ofReal s < ruinTime X x D ω) from hp).1
      have hs' : (s.toNNReal : ℝ) = s := Real.coe_toNNReal s hs
      have hp' : (s.toNNReal : ℝ) ∈ paymentTimes (ruinTime X x D ω) := by simpa only [hs'] using hp
      have hr := avram_wave4_03_actualStopped_theta_exponential_payment_kernel_dominated X x C D hD ω s.toNNReal hp' θ hθ q
      have hdiscount : Real.exp (θ * (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * q) ≤ Real.exp (θ * (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * X.ψ θ) := by
        apply Real.exp_le_exp.mpr
        have hsn : 0 ≤ (s.toNNReal : ℝ) := NNReal.coe_nonneg _
        nlinarith [mul_nonneg (sub_nonneg.mpr hq) hsn]
      have hreal : Real.exp (-(q * (s.toNNReal : ℝ))) ≤ Real.exp (θ * x) * Real.exp (θ * (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * X.ψ θ) := le_trans hr (mul_le_mul_of_nonneg_left hdiscount (Real.exp_nonneg (θ * x)))
      simp only [if_pos hp, c, g]
      simpa only [ENNReal.ofReal_mul (Real.exp_nonneg (θ * x))] using (ENNReal.ofReal_le_ofReal hreal)
    · simp only [if_neg hp, zero_le]
  have hinner (ω : Ω) : (∫⁻ s in Icc (0 : ℝ) (T : ℝ), if s ∈ paymentTimes (ruinTime X x D ω) then ENNReal.ofReal (Real.exp (-(q * (s.toNNReal : ℝ)))) else 0 ∂dividendMeasure D ω) ≤ c * (∫⁻ s in Icc (0 : ℝ) (T : ℝ), g ω s ∂dividendMeasure D ω) := by
    calc
      _ ≤ ∫⁻ s in Icc (0 : ℝ) (T : ℝ), c * g ω s ∂dividendMeasure D ω := lintegral_mono (hpoint ω)
      _ = _ := by rw [lintegral_const_mul]; exact hgm ω
  have hsource : a * (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ), g ω s ∂dividendMeasure D ω ∂P) ≤ 1 := by
    have hker (ω : Ω) (s : ℝ) : ENNReal.ofReal (θ * Real.exp (θ * (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * X.ψ θ)) = a * g ω s := by
      simpa only [a, g] using (ENNReal.ofReal_mul (le_of_lt hθ) : ENNReal.ofReal (θ * Real.exp (θ * (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * X.ψ θ)) = ENNReal.ofReal θ * ENNReal.ofReal (Real.exp (θ * (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * X.ψ θ)))
    have hinner' (ω : Ω) : (∫⁻ s in Icc (0 : ℝ) (T : ℝ), ENNReal.ofReal (θ * Real.exp (θ * (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * X.ψ θ)) ∂dividendMeasure D ω) = a * (∫⁻ s in Icc (0 : ℝ) (T : ℝ), g ω s ∂dividendMeasure D ω) := by
      simp_rw [hker ω]
      rw [lintegral_const_mul]; exact hgm ω
    calc
      _ = ∫⁻ ω, a * (∫⁻ s in Icc (0 : ℝ) (T : ℝ), g ω s ∂dividendMeasure D ω) ∂P := by rw [lintegral_const_mul]; exact hgo
      _ = ∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ), ENNReal.ofReal (θ * Real.exp (θ * (X.X s.toNNReal ω - rightLimit D s.toNNReal ω) - (s.toNNReal : ℝ) * X.ψ θ)) ∂dividendMeasure D ω ∂P := by
        apply lintegral_congr_ae
        filter_upwards [] with ω
        exact (hinner' ω).symm
      _ ≤ 1 := avram_wave4_03_sourceLevy_theta_scaled_closedHorizon_Icc_fullStieltjes_budget X D hD.1.1 θ hθ T hT
  calc
    _ ≤ a * (c * (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ), g ω s ∂dividendMeasure D ω ∂P)) := by
      apply mul_le_mul_of_nonneg_left
      calc
        _ ≤ ∫⁻ ω, c * (∫⁻ s in Icc (0 : ℝ) (T : ℝ), g ω s ∂dividendMeasure D ω) ∂P := lintegral_mono hinner
        _ = _ := by rw [lintegral_const_mul]; exact hgo
      positivity
    _ = c * (a * (∫⁻ ω, ∫⁻ s in Icc (0 : ℝ) (T : ℝ), g ω s ∂dividendMeasure D ω ∂P)) := by ac_rfl
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left hsource (by positivity)
    _ = ENNReal.ofReal (Real.exp (θ * x)) := by simp only [c, mul_one]
