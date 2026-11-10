-- Prove2me | solution 1 for AvramDividend.Classical.avram_gauss_ledger15_original_positive_clock_strict_martingale_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:36:48.128473+00:00
-- url     : https://prove2.me/submissions/25f8c43d-5d7e-4bad-9a18-26a455c5dbbf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_preexit_floor_stopped_c2_budget
import Theorems.Thm_AvramDividend_Classical_avram_gfinite15_original_preexit_floor_localisation_fatou_passage
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_positive_clock_mask_residual_identity
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_prepayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_initial_event_budget_to_condexp
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_condexp_upper_to_centred_witness

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical preexit source and its Fatou limit give a centred strict-clock certificate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω →
    0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0), (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0) (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτmeas : Measurable (fun ω => (τ ω : ℝ))) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0) (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) : ∀ k, ∃ M : Ω → ℝ,
    Integrable M P ∧ (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) ∧ (∀ᵐ ω ∂P, σ k ω ≠ 0 → Real.exp (-(q * (σ k ω : ℝ))) * w (riskProcess X x D (σ k ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal ≤ w x + M ω) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  have hLocal :=
    avram_gfinite15_original_preexit_floor_stopped_c2_budget
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ hσstop hσle
  have hAll :=
    avram_gfinite15_original_preexit_floor_localisation_fatou_passage
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ hσstop hσle hLocal
  let Z : Set Ω := {ω | σ k ω = 0}
  let S : Set Ω := Zᶜ
  let R : Ω → ℝ := fun ω =>
    Real.exp (-(q * (σ k ω : ℝ))) *
      w (riskProcess X x D (σ k ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal
  have hTermI : Integrable (fun ω =>
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (riskProcess X x D (σ k ω) ω)) P :=
    avram_ubv_finite13_original_stopped_prepayment_terminal_L1
      X x C hFiniteCap hxc D hD w hw_cont hw_neg
      q (le_of_lt hq) (σ k) (hσstop k)
  have hBound (ω : Ω) : σ k ω ≤ (n : ℝ≥0) := by
    calc
      σ k ω ≤ τ ω := hσle k ω
      _ = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := hτeq ω
      _ ≤ (n : ℝ≥0) := by
        have hle : min (ruinTime X x D ω) (n : ℝ≥0∞) ≤
            (n : ℝ≥0∞) := min_le_right _ _
        have hf : (n : ℝ≥0∞) ≠ ⊤ := by simp
        simpa using ENNReal.toNNReal_mono hf hle
  have hCashI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P :=
    avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
      X x C D hD q (le_of_lt hq) (σ k) (hσstop k) n hBound
  have hRI : Integrable R P := by
    exact hTermI.add hCashI
  let F : Ω → ℝ := fun ω => if ω ∈ Z then w x else R ω
  have hFI : Integrable F P := by
    have hZmeas : MeasurableSet Z := by
      have hnn : Measurable (σ k) :=
        measurable_coe_nnreal_ennreal_iff.mp (hσstop k).measurable'
      exact measurableSet_eq_fun hnn measurable_const
    have hParts :=
      ((integrable_const (w x)).indicator hZmeas).add
        (hRI.indicator hZmeas.compl)
    have hEq : F =
        (Z.indicator (fun _ : Ω => w x) + Zᶜ.indicator R) := by
      funext ω
      by_cases hz : ω ∈ Z <;> simp [F, Set.indicator, hz]
    rw [hEq]
    exact hParts
  have hBudget : ∀ A : Set Ω, MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, F ω ∂P) ≤ w x * (P A).toReal := by
    intro A hA
    have hAm : MeasurableSet A := (𝓕.rightCont).le 0 A hA
    have hZ : MeasurableSet Z := by
      have hnn : Measurable (σ k) :=
        measurable_coe_nnreal_ennreal_iff.mp (hσstop k).measurable'
      exact measurableSet_eq_fun hnn measurable_const
    have hMaskI : Integrable (fun ω => if ω ∈ Z then w x else R ω)
        (P.restrict A) := by
      have hc : Integrable (fun _ : Ω => w x) (P.restrict A) :=
        integrable_const _
      have hr : Integrable R (P.restrict A) := hRI.integrableOn
      have hparts := (hc.indicator hZ).add (hr.indicator hZ.compl)
      have hEq : (fun ω => if ω ∈ Z then w x else R ω) =
          (Z.indicator (fun _ : Ω => w x) + Zᶜ.indicator R) := by
        funext ω
        by_cases hz : ω ∈ Z <;> simp [Set.indicator, hz]
      rw [hEq]
      exact hparts
    have hId : (∫ ω in A, (if ω ∈ Z then w x else R ω) ∂P) -
        w x * (P A).toReal =
        (∫ ω in A ∩ S, R ω - w x ∂P) := by
      have ht := avram_p4_f12_positive_clock_mask_residual_identity
        (P.restrict A) Z hZ R hRI.integrableOn (w x)
      rw [MeasureTheory.integral_sub hMaskI (integrable_const (w x))] at ht
      have hRest : (P.restrict A).restrict Zᶜ = P.restrict (A ∩ S) := by
        simpa [S, Set.inter_comm] using
          (Measure.restrict_restrict (μ := P) (s := Zᶜ) (t := A) hZ.compl)
      have hConst : (∫ ω, w x ∂(P.restrict A)) =
          w x * (P A).toReal := by
        simp [hAm, Measure.real_def, mul_comm, smul_eq_mul]
      change (∫ ω, (if ω ∈ Z then w x else R ω) ∂(P.restrict A)) -
        (∫ ω, w x ∂(P.restrict A)) =
        (∫ ω, R ω - w x ∂((P.restrict A).restrict Zᶜ)) at ht
      rw [hRest, hConst] at ht
      exact ht
    have hPos : (∫ ω in A ∩ S, R ω ∂P) ≤
        w x * (P (A ∩ S)).toReal := by
      have hSet : S = {η : Ω | σ k η ≠ 0} := by
        ext η
        simp [S, Z]
      rw [hSet]
      exact hAll k A hA
    have hResidual : (∫ ω in A ∩ S, R ω - w x ∂P) ≤ 0 := by
      have hMeasAS : MeasurableSet (A ∩ S) := hAm.inter hZ.compl
      have hConstAS : (∫ ω in A ∩ S, w x ∂P) =
          w x * (P (A ∩ S)).toReal := by
        simp [integral_const, Measure.real_def, hMeasAS, smul_eq_mul, mul_comm]
      rw [MeasureTheory.integral_sub hRI.integrableOn (integrable_const (w x)), hConstAS]
      linarith
    have hGoal : (∫ ω in A, (if ω ∈ Z then w x else R ω) ∂P) ≤
        w x * (P A).toReal := by
      linarith
    simpa only [F, Z, Set.mem_setOf_eq] using hGoal
  have hCond :=
    avram_ubv_finite14_initial_event_budget_to_condexp
      (𝓕 := 𝓕) (P := P) F (w x) hFI hBudget
  obtain ⟨M, hMI, hMean, hMajor⟩ :=
    avram_ubv_finite12_condexp_upper_to_centred_witness
      (𝓕 := 𝓕) (P := P) (w x) F hFI hCond
  refine ⟨M, hMI, hMean, ?_⟩
  filter_upwards [hMajor] with ω hm
  intro hp
  simpa only [F, Z, Set.mem_setOf_eq, if_neg hp] using hm