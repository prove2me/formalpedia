-- Prove2me | solution 2 for AvramDividend.Classical.avram_ubv_loc6_zero_nu_topcap_positive_clock_gaussian_ito
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:30:57.535272+00:00
-- url     : https://prove2.me/submissions/b32e799f-69ad-497f-8443-b4e63f2a60e5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian11_conditional_budget_zero_clock_centering
import Theorems.Thm_AvramDividend_Classical_pure_jump_unbounded_variation_infinite_negative_activity
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_endpoint_original_F_le_masked_strict_cash
import Theorems.Thm_AvramDividend_Classical_avram_ubv_top12_original_zero_nu_positive_stopped_strict_one_martingale

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hTopCap : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω))
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) -
        w (riskProcess X x D t ω - (rightLimit D t ω - D t ω)))
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
          x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P) :
    ∀ k, ∃ Mc G R : Ω → ℝ,
      Integrable Mc P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∀ ω, σ k ω = 0 → Mc ω = 0) ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, σ k ω ≠ 0 → F k ω ≤ w x + Mc ω + G ω + R ω) := by
  classical
  intro k
  let A : Set Ω := {ω | σ k ω ≠ 0}
  have hA : MeasurableSet A := by
    convert (avram_p4_f12_stopped_nonnegative_clock_zero_event_measurable 𝓕 (σ k) (hσstop k)).compl using 1
    ext ω
    simp [A]
  letI : IsProbabilityMeasure P := X.isProbability
  by_cases hApos : 0 < (P A).toReal
  · have hsource_budget :
        (∫ ω in A, F k ω ∂P) ≤ w x * (P A).toReal := by
      have hσnonzero : X.σ ≠ 0 := by
        intro hz
        have hs := pure_jump_unbounded_variation_infinite_negative_activity X hz hBV
        simp [hν] at hs
      obtain ⟨M, hMI, hMzero, hStrict⟩ :=
        (avram_ubv_top12_original_zero_nu_positive_stopped_strict_one_martingale
          X hX hBV hσnonzero hν q hq w C hC hTopCap
          hw0 hw_cont hw_neg hw_smooth hw_gen hw_grad
          x hx hxc D hD hw_nonneg hjump
          n hn τ hτeq hτmeas hτstop
          W Cash Term hW hCash hTerm hTermMeas hCashI
          σ F hσstop hσle hFsource hFI) k
      have hEndpoint :=
        avram_ubv_gauss13_endpoint_original_F_le_masked_strict_cash
          X x C D hD w q (le_of_lt hq) hjump (σ k) (F k) (hFsource k)
      have hFullUpper : ∀ᵐ ω ∂P, F k ω ≤ w x + M ω := by
        filter_upwards [hStrict] with ω hω
        exact (hEndpoint ω).trans hω
      have hMoffIndicator : 0 ≤ᵐ[P] (Aᶜ.indicator M) := by
        filter_upwards [hStrict] with ω hω
        by_cases hz : σ k ω = 0
        · have hbound : w x ≤ w x + M ω := by
            simpa [hz] using hω
          have hm : 0 ≤ M ω := by linarith
          simpa [A, hz] using hm
        · simp [A, hz]
      have hMoff : 0 ≤ ∫ ω in Aᶜ, M ω ∂P := by
        rw [← integral_indicator hA.compl]; exact integral_nonneg_of_ae hMoffIndicator
      have hMonA : (∫ ω in A, M ω ∂P) ≤ 0 := by
        have hdecomp := integral_add_compl hA hMI
        rw [hMzero] at hdecomp
        linarith
      have hAddI : Integrable (fun ω => w x + M ω) P :=
        (integrable_const (w x)).add hMI
      have hLe : (∫ ω in A, F k ω ∂P) ≤
          ∫ ω in A, w x + M ω ∂P :=
        setIntegral_mono_ae (hFI k).integrableOn hAddI.integrableOn
          hFullUpper
      calc
        (∫ ω in A, F k ω ∂P) ≤
            ∫ ω in A, w x + M ω ∂P := hLe
        _ = w x * (P A).toReal + (∫ ω in A, M ω ∂P) := by
          rw [integral_add (integrable_const (w x)).integrableOn
            hMI.integrableOn, setIntegral_const]
          simp [smul_eq_mul, Measure.real, mul_comm]
        _ ≤ w x * (P A).toReal := by linarith
    obtain ⟨Mc, hMcI, hMcZero, hMcOff, hMcBound⟩ :=
      avram_ubv_gaussian11_conditional_budget_zero_clock_centering
        A hA hApos (F k) (hFI k) (w x) hsource_budget
    refine ⟨Mc, 0, 0, hMcI, hMcZero, ?_, ?_, ?_, ?_⟩
    · intro ω hzero
      apply hMcOff
      simp [A, hzero]
    · filter_upwards [] with ω
      exact le_rfl
    · filter_upwards [] with ω
      exact le_rfl
    · filter_upwards [] with ω
      intro hclock
      simpa using hMcBound ω hclock
  · have hAre : (P A).toReal = 0 :=
      le_antisymm (le_of_not_gt hApos) ENNReal.toReal_nonneg
    have hAzero : P A = 0 := by
      have hh := ENNReal.ofReal_toReal (measure_ne_top P A)
      rw [hAre] at hh
      simpa using hh.symm
    have houtside : ∀ᵐ ω ∂P, ω ∉ A := by
      rw [MeasureTheory.ae_iff]
      have hset : {a : Ω | ¬ a ∉ A} = A := by ext ω; simp
      simpa only [hset] using hAzero
    refine ⟨0, 0, 0, by simp, by simp, by simp, by simp, by simp, ?_⟩
    filter_upwards [houtside] with ω hω
    intro hclock
    exact False.elim (hω (show ω ∈ A from hclock))
