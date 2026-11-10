-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite15_original_preexit_floor_localisation_fatou_passage
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T04:18:11.155226+00:00
-- url     : https://prove2.me/submissions/0527a99b-5701-46a2-b520-8b2eecddf766

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_avram_gfinite30_original_lower_exit_pathwise_floor_clocks
import Theorems.Thm_AvramDividend_Classical_avram_gfinite31_positive_clock_event_uniform_budget
import Theorems.Thm_AvramDividend_Classical_avram_gfinite26_original_cofinal_strict_reward_ae_limit
import Theorems.Thm_AvramDividend_Classical_avram_gfinite27_original_strict_stopped_rewards_global_meas
import Theorems.Thm_AvramDividend_Classical_avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
import Theorems.Thm_AvramDividend_Classical_avram_gfinite29_original_masked_positive_event_fatou
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_initial_value_nonnegative
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hLocal : ∀ k (ρ : Ω → ℝ≥0)
      (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
      (hρle : ∀ ω, ρ ω ≤ σ k ω) (δ : ℝ) (hδ : 0 < δ)
      (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω → δ ≤ riskProcess X x D t ω)
      (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A ∩ {η : Ω | ρ η ≠ 0},
        Real.exp (-(q * (ρ ω : ℝ))) * w (riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
        w x * (P (A ∩ {η : Ω | ρ η ≠ 0})).toReal) :
    ∀ k (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A ∩ {η : Ω | σ k η ≠ 0},
        Real.exp (-(q * (σ k ω : ℝ))) * w (riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ∂P) ≤
        w x * (P (A ∩ {η : Ω | σ k η ≠ 0})).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k A hA
  have hAglobal : MeasurableSet A := (𝓕.rightCont.le 0) A hA
  have hσruin : ∀ ω, (σ k ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    intro ω
    calc
      (σ k ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := by exact_mod_cast hσle k ω
      _ ≤ ruinTime X x D ω := by
        rw [hτeq ω]
        exact (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.2 ω
  have hσbound : ∀ ω, σ k ω ≤ (n : ℝ≥0) := by
    intro ω
    calc
      σ k ω ≤ τ ω := hσle k ω
      _ ≤ (n : ℝ≥0) := by
        rw [hτeq ω]
        exact (avram_wave7_08_source_truncated_clock_nnreal_bounds X x D n).2.1 ω
  obtain ⟨L, hLstop, hLle, hLmono, hLlim, hLfloor⟩ :=
    avram_gfinite30_original_lower_exit_pathwise_floor_clocks
      X hBV x C D hD (σ k) (hσstop k) hσruin
  let R : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω =>
    Real.exp (-(q * (ζ ω : ℝ))) * w (riskProcess X x D (ζ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ζ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let H : (Ω → ℝ≥0) → Ω → ℝ := fun ζ ω =>
    if ζ ω = 0 then w x else R ζ ω
  have hLm (j : ℕ) : Measurable (L j) := measurable_coe_nnreal_ennreal_iff.mp (hLstop j).measurable'
  have hσm : Measurable (σ k) := measurable_coe_nnreal_ennreal_iff.mp (hσstop k).measurable'
  have hMeas := avram_gfinite27_original_strict_stopped_rewards_global_meas
    X q w hw_cont hw_neg x C D hD (σ k) (hσstop k) L hLstop
  change (∀ j, Measurable (H (L j))) ∧
    AEStronglyMeasurable (H (σ k)) P at hMeas
  have hInt : ∀ j, Integrable (H (L j)) P := by
    intro j
    change Integrable (fun ω => if L j ω = 0 then w x else
      Real.exp (-(q * (L j ω : ℝ))) * w (riskProcess X x D (L j ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (L j ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) P
    exact avram_gfinite28_original_bounded_stop_masked_strict_reward_L1
      X x C hFiniteCap hxc D hD w hw_cont hw_neg q hq (L j)
        (hLstop j) (n : ℝ≥0)
        (fun ω => (hLle j ω).trans (hσbound ω))
  have hPos (ζ : Ω → ℝ≥0) (ω : Ω) (hζ : ζ ω ≠ 0) :
      0 ≤ H ζ ω := by
    have hy : 0 ≤ w (riskProcess X x D (ζ ω) ω) := by
      by_cases hy0 : 0 ≤ riskProcess X x D (ζ ω) ω
      · exact avram_p4_e_localise_original_anycap_payoff_nonnegative_from_source_interior_gradient
          w C hw0 hw_cont hw_smooth hw_grad _ hy0
          (hD.2 ω (ζ ω) (pos_iff_ne_zero.mpr hζ))
      · rw [hw_neg _ (lt_of_not_ge hy0)]
    simp only [H, if_neg hζ]
    change 0 ≤ R ζ ω
    exact add_nonneg (mul_nonneg (le_of_lt (Real.exp_pos _)) hy)
      ENNReal.toReal_nonneg
  have hWx : 0 ≤ w x :=
    avram_p3_bv_initial_value_nonnegative C hC w hw_cont hw0
      (hw_smooth.of_le (by norm_num)) hw_grad x (le_of_lt hx) hxc
  have hLocalB : ∀ j,
      (∫ ω in A ∩ {η : Ω | L j η ≠ 0}, R (L j) ω ∂P) ≤
      w x * (P (A ∩ {η : Ω | L j η ≠ 0})).toReal := by
    intro j
    exact hLocal k (L j) (hLstop j) (hLle j)
      ((1 : ℝ) / ((j : ℝ) + 1)) (by positivity) (hLfloor j) A hA
  have hBudget := avram_gfinite31_positive_clock_event_uniform_budget
    P A hAglobal (σ k) L hLm hLle R (w x) hWx hLocalB
  change ∀ j, (∫ ω in A ∩ {η : Ω | L j η ≠ 0},
    H (L j) ω ∂P) ≤
    w x * (P (A ∩ {η : Ω | σ k η ≠ 0})).toReal at hBudget
  have hHlim := avram_gfinite26_original_cofinal_strict_reward_ae_limit
    X hν q hq w hw_cont x C D hD n τ hτeq
      (σ k) (hσle k) L hLle hLmono hLlim
  change ∀ᵐ ω ∂P, Tendsto (fun j => ENNReal.ofReal (H (L j) ω))
    atTop (𝓝 (ENNReal.ofReal (H (σ k) ω))) at hHlim
  let b : ℝ := w x * (P (A ∩ {η : Ω | σ k η ≠ 0})).toReal
  have hb : 0 ≤ b := mul_nonneg hWx ENNReal.toReal_nonneg
  have hFatou := avram_gfinite29_original_masked_positive_event_fatou
    P A hAglobal (σ k) hσm L hLm hLle hLlim H
      hMeas.1 hMeas.2 hInt (fun j ω h => hPos (L j) ω h)
      (hPos (σ k)) hHlim b hb hBudget
  have hNonzero : MeasurableSet {ω : Ω | σ k ω ≠ 0} := by
    have hz : MeasurableSet {ω : Ω | σ k ω = 0} :=
      hσm (measurableSet_singleton (0 : ℝ≥0))
    simpa only [Set.compl_setOf] using hz.compl
  have hE : MeasurableSet (A ∩ {η : Ω | σ k η ≠ 0}) :=
    hAglobal.inter hNonzero
  change (∫ ω in A ∩ {η : Ω | σ k η ≠ 0}, R (σ k) ω ∂P) ≤ b
  calc
    (∫ ω in A ∩ {η : Ω | σ k η ≠ 0}, R (σ k) ω ∂P) =
        (∫ ω in A ∩ {η : Ω | σ k η ≠ 0}, H (σ k) ω ∂P) := by
          apply setIntegral_congr_fun hE
          intro ω hω
          simp only [H, if_neg hω.2]
    _ ≤ b := hFatou
