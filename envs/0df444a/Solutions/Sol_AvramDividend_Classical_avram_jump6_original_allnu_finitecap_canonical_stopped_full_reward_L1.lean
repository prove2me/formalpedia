-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_original_allnu_finitecap_canonical_stopped_full_reward_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T21:06:42.628713+00:00
-- url     : https://prove2.me/submissions/497d4ef6-e86c-4b9b-a0ca-daec09f7758d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_any_stopped_terminal_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite12_positive_clock_initial_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every finite-cap exact canonical original stopped dividend reward is
L1, regardless of Gaussian coefficient or negative Lévy jump activity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hFinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    AEStronglyMeasurable Term P ∧
    Integrable Cash P ∧
    Integrable Term P ∧
    Integrable (fun ω => Term ω + Cash ω) P ∧
    MeasurableSet[𝓕.rightCont 0] {ω : Ω | τ ω ≠ 0} := by
  obtain ⟨hTermM, hCashI⟩ :=
    avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
      X x C D hD w hw_cont hw_neg q n τ hτeq hτmeas hτstop
      W Cash Term hW hCash hTerm
  have hTermI : Integrable Term P :=
    avram_ubv_finite9_original_any_stopped_terminal_integrable
      X x C hFinite hxc w hw_cont hw_neg D hD
      τ W Term hW q hq hTerm hTermM
  have hEvent : MeasurableSet[𝓕.rightCont 0]
      {ω : Ω | τ ω ≠ 0} :=
    avram_ubv_finite12_positive_clock_initial_measurable τ hτstop
  exact ⟨hTermM, hCashI, hTermI, hTermI.add hCashI, hEvent⟩

