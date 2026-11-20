-- Prove2me | solution 7 for AvramDividend.Classical.avram_jump6_E_topcap_original_positive_clock_expected_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T23:53:30.399517+00:00
-- url     : https://prove2.me/submissions/020e183c-0419-468b-8f36-1896dc8b76d4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_E_infinite_original_single_clock_physical_signed_source
import Theorems.Thm_AvramDividend_Classical_avram_jump6_E_topcap_original_same_clock_condexp_ito_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_jump11_past_event_integral_of_condexp_zero
import Theorems.Thm_AvramDividend_Classical_avram_b21_initial_event_local_aggregate_budget
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
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
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hTop : C = ⊤) :
    ∀ k, (∫ ω in {ω : Ω | σ k ω ≠ 0}, F k ω ∂P) ≤
      w x * (P {ω : Ω | σ k ω ≠ 0}).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro k
  let A : Set Ω := {ω | σ k ω ≠ 0}
  have hA : MeasurableSet[𝓕.rightCont 0] A :=
    avram_ubv_finite12_positive_clock_initial_measurable
      (σ k) (hσstop k)
  obtain ⟨M, hMI, hCE, hUpper⟩ :
      ∃ M : Ω → ℝ, Integrable M P ∧
        (∀ᵐ ω ∂P, condExp (𝓕.rightCont 0) P M ω = 0) ∧
        (∀ᵐ ω ∂P, F k ω ≤ w x + M ω) := by
    by_cases hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤
    · obtain ⟨hσMeas, hFMeas, M, G, R, hMI, hCE, hG, hR, hBound⟩ :=
        avram_jump6_E_infinite_original_single_clock_physical_signed_source
          X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
          hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
          n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
          hTermMeas hCashI σ F hσstop hσle hFsource hFI hTop
          hInfiniteActivity k
      refine ⟨M, hMI, hCE, ?_⟩
      filter_upwards [hBound, hG, hR] with ω hb hg hr
      linarith
    · exact avram_jump6_E_topcap_original_same_clock_condexp_ito_majorant
        X hX hBV hν hσ q hq w C hC hw0 hw_cont hw_neg
        hw_smooth hw_gen hw_grad x hx hxc D hD hw_nonneg hjump
        n hn τ hτeq hτmeas hτstop W Cash Term hW hCash hTerm
        hTermMeas hCashI σ F hσstop hσle hFsource hFI hTop k
  have hMzero : (∫ ω in A, M ω ∂P) = 0 :=
    avram_ubv_jump11_past_event_integral_of_condexp_zero
      (𝓕.rightCont 0) (𝓕.rightCont.le 0) M hMI hCE A hA
  have hUpperA : ∀ᵐ ω ∂(P.restrict A),
      F k ω ≤ w x + M ω + (0 : ℝ) := by
    filter_upwards [ae_restrict_of_ae hUpper] with ω hb
    linarith
  have hBudget := avram_b21_initial_event_local_aggregate_budget
    A hA (w x) (F k) M (fun _ => (0 : ℝ))
    (hFI k).integrableOn hMI.integrableOn (by simp)
    hMzero hUpperA
  simpa only [integral_zero, add_zero] using hBudget
