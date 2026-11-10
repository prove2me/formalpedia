-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite13_original_strict_gaussian_condexp_HJB_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T08:01:27.980217+00:00
-- url     : https://prove2.me/submissions/4c5dea96-fdaf-4c67-99a4-c2dc67522cd3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_prepayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_original_gaussian_strict_stopped_event_budget
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite14_initial_event_budget_to_condexp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
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
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont 0) P
        (fun η => if σ k η = 0 then w x else
          Real.exp (-(q * (σ k η : ℝ))) *
            w (riskProcess X x D (σ k η) η) +
          (∫⁻ s in paymentTimes (ruinTime X x D η) ∩ Iio (σ k η : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D η)).toReal) ω ≤ w x := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  have hBound (ω : Ω) : σ k ω ≤ (n : ℝ≥0) := by
    calc
      σ k ω ≤ τ ω := hσle k ω
      _ = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := hτeq ω
      _ ≤ (n : ℝ≥0) := by
        have hle : min (ruinTime X x D ω) (n : ℝ≥0∞) ≤
            (n : ℝ≥0∞) := min_le_right _ _
        have hf : (n : ℝ≥0∞) ≠ ⊤ := by simp
        simpa using ENNReal.toNNReal_mono hf hle
  have hTermI : Integrable (fun ω =>
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (riskProcess X x D (σ k ω) ω)) P :=
    avram_ubv_finite13_original_stopped_prepayment_terminal_L1
      X x C hFiniteCap hxc D hD w hw_cont hw_neg
      q (le_of_lt hq) (σ k) (hσstop k)
  have hCashI : Integrable (fun ω =>
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) P :=
    avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
      X x C D hD q (le_of_lt hq) (σ k) (hσstop k) n hBound
  let H : Ω → ℝ := fun ω =>
    if σ k ω = 0 then w x else
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
  have hZero : MeasurableSet {ω : Ω | σ k ω = 0} := by
    have hnn : Measurable (σ k) :=
      measurable_coe_nnreal_ennreal_iff.mp (hσstop k).measurable'
    exact measurableSet_eq_fun hnn measurable_const
  have hHI : Integrable H P := by
    have hConst : Integrable (fun _ : Ω => w x) P := integrable_const _
    have hSum : Integrable (fun ω =>
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal) P := hTermI.add hCashI
    have hI := (hConst.indicator hZero).add
      (hSum.indicator hZero.compl)
    have hEq : H = (fun ω : Ω =>
        ({η : Ω | σ k η = 0}).indicator (fun _ => w x) ω +
        ({η : Ω | σ k η ≠ 0}).indicator (fun η =>
          Real.exp (-(q * (σ k η : ℝ))) *
            w (riskProcess X x D (σ k η) η) +
          (∫⁻ s in paymentTimes (ruinTime X x D η) ∩ Iio (σ k η : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D η)).toReal) ω) := by
      funext ω
      by_cases hs : σ k ω = 0
      · simp [H, Set.indicator, hs]
      · simp [H, Set.indicator, hs]
    rw [hEq]
    exact hI
  have hBudget : ∀ (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A, H ω ∂P) ≤ w x * (P A).toReal := by
    intro A hA
    exact avram_ubv_finite14_original_gaussian_strict_stopped_event_budget
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump n hn τ
      hτeq hτmeas hτstop σ hσstop hσle k A hA
  exact avram_ubv_finite14_initial_event_budget_to_condexp
    H (w x) hHI hBudget
