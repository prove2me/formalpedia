-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_original_canonical_true_stopped_reward_measurable_Cash_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T19:53:21.60253+00:00
-- url     : https://prove2.me/submissions/8ba328f4-e11c-413d-a02e-6b60c7306281

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The full original stopped reward construction is canonical: the Proved
existential measurable/integrable source fixes W, Cash and Term pointwise
and therefore transfers the properties to arbitrary source-faithful names. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (n : ℕ) (τ : Ω → ℝ≥0)
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
    AEStronglyMeasurable Term P ∧ Integrable Cash P := by
  obtain ⟨W', Cash', Term', hW', hCash', hTerm', hTermM', hCashI'⟩ :=
    avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
      X x C D hD w hw_cont hw_neg q n τ hτeq hτmeas hτstop
  have hWEq : W = W' := by
    funext ω
    calc
      W ω =
        (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) := hW ω
      _ = W' ω := (hW' ω).symm
  have hCashEq : Cash = Cash' := by
    funext ω
    calc
      Cash ω =
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal := hCash ω
      _ = Cash' ω := (hCash' ω).symm
  have hTermEq : Term = Term' := by
    funext ω
    calc
      Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω) :=
        hTerm ω
      _ = Real.exp (-(q * (τ ω : ℝ))) * w (W' ω) := by
        rw [hWEq]
      _ = Term' ω := (hTerm' ω).symm
  constructor
  · simpa only [hTermEq] using hTermM'
  · simpa only [hCashEq] using hCashI'

