-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_any_discount_finite_horizon_stieltjes_exp_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T12:09:46.654199+00:00
-- url     : https://prove2.me/submissions/a2049cf6-db4b-48f7-a1fd-c799cad0c6dc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_03_original_stopped_fullStieltjes_realDiscount_payoff_le_expCapital
import Theorems.Thm_AvramDividend_Classical_paymentTimes_membership_to_nNReal_active
import Theorems.Thm_AvramDividend_Classical_paymentTimes_measurable
import Theorems.Thm_AvramDividend_Classical_paymentTimes_joint_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_global_sfinite_kernel_exists
import Theorems.Thm_AvramDividend_Classical_measurable_random_indicator_lintegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Original finite-horizon stopped full-Stieltjes reward at an arbitrary
discount is controlled by the proved exponential Lévy test and its exact
s-finite random dividend-measure kernel. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : 0 < T) (q : ℝ) :
    (∫⁻ ω, ∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω) ∂P) ≤
    ENNReal.ofReal (Real.exp (|X.ψ 1 - q| * (T : ℝ))) *
      ENNReal.ofReal (Real.exp x) := by
  let τ : Ω → ℝ≥0∞ := ruinTime X x D
  let K : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (|X.ψ 1 - q| * (T : ℝ)))
  let wψ : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (Real.exp (-(X.ψ 1 * s)))
  let wq : ℝ → ℝ≥0∞ := fun s =>
    ENNReal.ofReal (Real.exp (-(q * s)))
  let E : Ω → Set ℝ := fun ω => paymentTimes (τ ω) ∩ Iic (T : ℝ)
  have hE (ω : Ω) : MeasurableSet (E ω) :=
    (paymentTimes_measurable (τ ω)).inter measurableSet_Iic
  have hτ : Measurable τ := ruinTime_measurable X x D hD.1.1
  let S : Set (ℝ × Ω) :=
    {p | p.1 ∈ paymentTimes (τ p.2) ∧ p.1 ≤ (T : ℝ)}
  have hS : MeasurableSet S :=
    (paymentTimes_joint_measurable τ hτ).inter
      (measurableSet_le measurable_fst measurable_const)
  have hwψ : Measurable wψ :=
    ENNReal.measurable_ofReal.comp
      (Real.continuous_exp.measurable.comp
        ((measurable_const.mul measurable_id).neg))
  obtain ⟨κ, hκs, hκ⟩ :=
    dividendMeasure_global_sfinite_kernel_exists D hD.1.1
  letI : IsSFiniteKernel κ := hκs
  have hRψ : Measurable (fun ω : Ω =>
      ∫⁻ s in E ω, wψ s ∂(dividendMeasure D ω)) := by
    have hm := measurable_random_indicator_lintegral κ S hS wψ hwψ
    have heq : (fun ω : Ω =>
        ∫⁻ s in E ω, wψ s ∂(dividendMeasure D ω)) =
        (fun ω : Ω =>
          ∫⁻ s, if (s, ω) ∈ S then wψ s else 0 ∂κ ω) := by
      funext ω
      rw [hκ ω]
      rw [← lintegral_indicator (hE ω) wψ]
      apply lintegral_congr
      intro s
      by_cases hs : s ∈ E ω
      · have hsS : (s, ω) ∈ S := by exact hs
        simp [Set.indicator, hs, hsS]
      · have hsS : (s, ω) ∉ S := by
          intro h
          exact hs h
        simp [Set.indicator, hs, hsS]
    rw [heq]
    simpa only [S, Set.mem_setOf_eq] using hm
  have hPoint (ω : Ω) (s : ℝ) (hs : s ∈ E ω) :
      wq s ≤ K * wψ s := by
    have hs0 : 0 ≤ s :=
      (paymentTimes_membership_to_nNReal_active (τ ω) s hs.1).1
    have hsT : s ≤ (T : ℝ) := hs.2
    have hDelta :
        (X.ψ 1 - q) * s ≤ |X.ψ 1 - q| * (T : ℝ) := by
      calc
        (X.ψ 1 - q) * s ≤ |X.ψ 1 - q| * s :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hs0
        _ ≤ |X.ψ 1 - q| * (T : ℝ) :=
          mul_le_mul_of_nonneg_left hsT (abs_nonneg _)
    have hReal : Real.exp (-(q * s)) ≤
        Real.exp (|X.ψ 1 - q| * (T : ℝ)) *
          Real.exp (-(X.ψ 1 * s)) := by
      calc
        Real.exp (-(q * s)) =
            Real.exp ((X.ψ 1 - q) * s) *
              Real.exp (-(X.ψ 1 * s)) := by
                rw [← Real.exp_add]
                congr 1
                ring
        _ ≤ Real.exp (|X.ψ 1 - q| * (T : ℝ)) *
              Real.exp (-(X.ψ 1 * s)) :=
          mul_le_mul_of_nonneg_right
            ((Real.exp_le_exp).2 hDelta) (Real.exp_nonneg _)
    change ENNReal.ofReal (Real.exp (-(q * s))) ≤
      ENNReal.ofReal (Real.exp (|X.ψ 1 - q| * (T : ℝ))) *
        ENNReal.ofReal (Real.exp (-(X.ψ 1 * s)))
    rw [← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _))]
    exact ENNReal.ofReal_le_ofReal hReal
  have hInner (ω : Ω) :
      (∫⁻ s in E ω, wq s ∂(dividendMeasure D ω)) ≤
        K * (∫⁻ s in E ω, wψ s ∂(dividendMeasure D ω)) := by
    have hpt : (E ω).indicator wq ≤
        (fun s : ℝ => K * (E ω).indicator wψ s) := by
      intro s
      by_cases hs : s ∈ E ω
      · simpa [Set.indicator, hs] using hPoint ω s hs
      · simp [Set.indicator, hs]
    calc
      (∫⁻ s in E ω, wq s ∂(dividendMeasure D ω)) =
          (∫⁻ s, (E ω).indicator wq s ∂(dividendMeasure D ω)) :=
        (lintegral_indicator (hE ω) wq).symm
      _ ≤ ∫⁻ s, K * (E ω).indicator wψ s
          ∂(dividendMeasure D ω) :=
        lintegral_mono hpt
      _ = K * (∫⁻ s, (E ω).indicator wψ s
          ∂(dividendMeasure D ω)) :=
        lintegral_const_mul K (hwψ.indicator (hE ω))
      _ = K * (∫⁻ s in E ω, wψ s
          ∂(dividendMeasure D ω)) := by
        rw [lintegral_indicator (hE ω) wψ]
  have hsource :=
    avram_wave4_03_original_stopped_fullStieltjes_realDiscount_payoff_le_expCapital
      X x C D hD T hT
  change (∫⁻ ω, ∫⁻ s in E ω, wq s
      ∂(dividendMeasure D ω) ∂P) ≤
    K * ENNReal.ofReal (Real.exp x)
  calc
    (∫⁻ ω, ∫⁻ s in E ω, wq s
        ∂(dividendMeasure D ω) ∂P) ≤
        ∫⁻ ω, K * (∫⁻ s in E ω, wψ s
          ∂(dividendMeasure D ω)) ∂P :=
      lintegral_mono hInner
    _ = K * (∫⁻ ω, ∫⁻ s in E ω, wψ s
          ∂(dividendMeasure D ω) ∂P) :=
      lintegral_const_mul K hRψ
    _ ≤ K * ENNReal.ofReal (Real.exp x) :=
      mul_le_mul_of_nonneg_left hsource bot_le
