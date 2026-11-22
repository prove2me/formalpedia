-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerF_original_rightmesh_allbounded_clipped_expected_cash_budget_v1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:48:57.667695+00:00
-- url     : https://prove2.me/submissions/2d11558c-ec11-4e61-90fb-6ddf7122a9f8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_zero_time_postpayment_within_cap
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_physical_rightmesh_isStoppingTime
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerF_original_rightmesh_positive_clock_restricted_ennreal_expected_budget_v1
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (q : ℝ) (hq :
    0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧
    ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y →
    ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
    (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess
    X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (W Cash Term : Ω → ℝ) (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω :
    ℝ≥0∞) < ruinTime X x D ω then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω) (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic
    (τ ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) (hTermMeas :
    AEStronglyMeasurable Term P) (hCashI : Integrable Cash P) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ) (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) (hFsource : ∀ k ω, F k ω = Real.exp (-(q * (σ k ω : ℝ))) * w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ k ω) ω -
    rightLimit D (σ k ω) ω else riskProcess X x D (σ k ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s)))
    ∂(dividendMeasure D ω)).toReal) (hFI : ∀ k, Integrable (F k) P) :
    ∀ (k m : ℕ),
      let ρ : Ω → ℝ≥0 := fun ω => min (τ ω) (σ k ω + ((1 : ℝ≥0) / ((m : ℝ≥0) + 1)))
      let V : ℝ → ℝ := fun z => if ENNReal.ofReal z ≤ C then w z else w C.toReal + (z - C.toReal)
      let Approx : Ω → ℝ := fun ω =>
        Real.exp (-(q * (ρ ω : ℝ))) * V (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω else riskProcess X x D (ρ ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      (∫⁻ ω, ENNReal.ofReal (Approx ω) ∂P) ≤ ENNReal.ofReal (w x) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k m
  let ρ : Ω → ℝ≥0 := fun ω => min (τ ω) (σ k ω + (1 / ((m : ℝ≥0) + 1)))
  let V : ℝ → ℝ := fun z => if ENNReal.ofReal z ≤ C then w z
    else w C.toReal + (z - C.toReal)
  let Approx : Ω → ℝ := fun ω =>
    Real.exp (-(q * (ρ ω : ℝ))) *
      V (if ρ ω = 0 ∨ (ρ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (ρ ω) ω - rightLimit D (ρ ω) ω
      else riskProcess X x D (ρ ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (ρ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  have hStop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)) :=
    avram_f6_original_physical_rightmesh_isStoppingTime
      τ (σ k) hτstop (hσstop k) (1 / ((m : ℝ≥0) + 1))
  have hA : MeasurableSet {ω : Ω | ρ ω = 0} :=
    measurableSet_eq_fun
      (measurable_coe_nnreal_ennreal_iff.mp hStop.measurable')
      measurable_const
  have hZero (ω : Ω) (hz : ρ ω = 0) : Approx ω ≤ w x := by
    let F₀ : Ω → ℝ := fun η =>
      Real.exp (-(q * (ρ η : ℝ))) *
        w (if ρ η = 0 ∨ (ρ η : ℝ≥0∞) < ruinTime X x D η then
          x + X.X (ρ η) η - rightLimit D (ρ η) η
        else riskProcess X x D (ρ η) η) +
      (∫⁻ s in paymentTimes (ruinTime X x D η) ∩ Iic (ρ η : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D η)).toReal
    have hSource : F₀ ω ≤ w x :=
      avram_ubv_loc6_original_exact_localised_F_zero_clock_le_initial
        X x q w C D hD hjump ρ F₀ (by intro η; rfl) ω hz
    have hCap : ENNReal.ofReal (x + X.X 0 ω - rightLimit D 0 ω) ≤ C :=
      (avram_p4_e_localise_original_zero_time_postpayment_within_cap X x C hxc D hD ω).2
    have hEq : Approx ω = F₀ ω := by simp [Approx, F₀, hz, V, hCap]
    exact hEq.le.trans hSource
  have hZeroI : (∫⁻ ω in {ω : Ω | ρ ω = 0}, ENNReal.ofReal (Approx ω) ∂P) ≤
      ENNReal.ofReal (w x) * P {ω : Ω | ρ ω = 0} := by
    calc
      _ ≤ ∫⁻ ω in {ω : Ω | ρ ω = 0}, ENNReal.ofReal (w x) ∂P := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hA] with ω hω
        exact ENNReal.ofReal_le_ofReal (hZero ω hω)
      _ = _ := setLIntegral_const _ _
  have hPos :
      (∫⁻ ω in {ω : Ω | ρ ω ≠ 0}, ENNReal.ofReal (Approx ω) ∂P) ≤
        ENNReal.ofReal (w x) * P {ω : Ω | ρ ω ≠ 0} := by
    exact avram_pj_workerF_original_rightmesh_positive_clock_restricted_ennreal_expected_budget_v1
      X hX hBV q hq w C hC hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad x hx
      hxc D hD hw_nonneg hjump n hn τ hτeq hτmeas hτstop W Cash Term hW
      hCash hTerm hTermMeas hCashI σ F hσstop hσle hFsource hFI k m
  have hTotal : P {ω : Ω | ρ ω = 0} + P {ω : Ω | ρ ω ≠ 0} = 1 := by
    have hm : P {ω : Ω | ρ ω = 0} + P ({ω : Ω | ρ ω = 0}ᶜ) = P Set.univ :=
      measure_add_measure_compl hA
    simpa only [Set.compl_setOf, measure_univ] using hm
  calc
    (∫⁻ ω, ENNReal.ofReal (Approx ω) ∂P) =
        (∫⁻ ω in {ω : Ω | ρ ω = 0}, ENNReal.ofReal (Approx ω) ∂P) +
        (∫⁻ ω in {ω : Ω | ρ ω ≠ 0}, ENNReal.ofReal (Approx ω) ∂P) := by
      simpa only [Set.compl_setOf] using
        (lintegral_add_compl (fun ω => ENNReal.ofReal (Approx ω)) hA).symm
    _ ≤ ENNReal.ofReal (w x) * P {ω : Ω | ρ ω = 0} +
        ENNReal.ofReal (w x) * P {ω : Ω | ρ ω ≠ 0} :=
      add_le_add hZeroI hPos
    _ = ENNReal.ofReal (w x) := by
      rw [← mul_add, hTotal, mul_one]
