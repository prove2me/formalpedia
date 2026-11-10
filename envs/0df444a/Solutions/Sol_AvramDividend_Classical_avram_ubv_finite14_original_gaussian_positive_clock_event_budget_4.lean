-- Prove2me | solution 4 for AvramDividend.Classical.avram_ubv_finite14_original_gaussian_positive_clock_event_budget
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:17:22.949701+00:00
-- url     : https://prove2.me/submissions/0a6b8df8-01bc-4e10-bc82-e689740f2ec0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gauss_ledger15_original_positive_clock_strict_martingale_certificate
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_prepayment_terminal_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_bounded_stopped_strict_cash_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_turn11_initial_filtration_ae_martingale_budget

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original centred physical source certificate implies the positive-clock conditional event budget. -/
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
    ∀ k (A : Set Ω), MeasurableSet[𝓕.rightCont 0] A →
      (∫ ω in A ∩ {η : Ω | σ k η ≠ 0},
        (Real.exp (-(q * (σ k ω : ℝ))) *
            w (riskProcess X x D (σ k ω) ω) +
          (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
            ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) ∂P) ≤
          w x * (P (A ∩ {η : Ω | σ k η ≠ 0})).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k A hA
  obtain ⟨M, hMI, hMean, hMajor⟩ :=
    avram_gauss_ledger15_original_positive_clock_strict_martingale_certificate
      X hX hBV hν q hq w C hC hFiniteCap hw0 hw_cont hw_neg
      hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
      n hn τ hτeq hτmeas hτstop σ hσstop hσle k
  let S : Set Ω := {ω | σ k ω ≠ 0}
  let R : Ω → ℝ := fun ω =>
    Real.exp (-(q * (σ k ω : ℝ))) *
      w (riskProcess X x D (σ k ω) ω) +
    (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (σ k ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal
  let F : Ω → ℝ := fun ω =>
    if σ k ω = 0 then w x + M ω else R ω
  have hS : MeasurableSet[𝓕.rightCont 0] S :=
    avram_ubv_finite12_positive_clock_initial_measurable
      (𝓕 := 𝓕) (σ k) (hσstop k)
  have hSm : MeasurableSet S := (𝓕.rightCont).le 0 S hS
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
  have hRI : Integrable R P := hTermI.add hCashI
  have hFI : Integrable F P := by
    have hFirst : Integrable (fun ω => w x + M ω) P :=
      (integrable_const (w x)).add hMI
    have hParts :=
      (hFirst.indicator hSm.compl).add (hRI.indicator hSm)
    have heq : F =
        (Sᶜ.indicator (fun ω => w x + M ω) + S.indicator R) := by
      funext ω
      by_cases hz : σ k ω = 0 <;> simp [F, S, Set.indicator, hz]
    rw [heq]
    exact hParts
  have hUpper : ∀ᵐ ω ∂P, F ω ≤ w x + M ω := by
    filter_upwards [hMajor] with ω hm
    by_cases hz : σ k ω = 0
    · simp [F, hz]
    · simpa only [F, if_neg hz] using hm hz
  have hBudget :=
    avram_ubv_finite9_turn11_initial_filtration_ae_martingale_budget
      (𝓕 := 𝓕) (P := P) (w x) F M hFI hMI hMean hUpper
  have hE : MeasurableSet[𝓕.rightCont 0] (A ∩ S) := hA.inter hS
  have hEm : MeasurableSet (A ∩ S) :=
    (𝓕.rightCont).le 0 (A ∩ S) hE
  have hIntEq : (∫ ω in A ∩ S, F ω ∂P) =
      (∫ ω in A ∩ S, R ω ∂P) := by
    apply setIntegral_congr_fun hEm
    intro ω hω
    have hp : σ k ω ≠ 0 := hω.2
    simp [F, hp]
  have hResult := hBudget (A ∩ S) hE
  rw [hIntEq] at hResult
  simpa only [S] using hResult
