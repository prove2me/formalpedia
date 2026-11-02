-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_06_original_actual_piecewise_discounted_terminal_auto_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T23:33:46.278995+00:00
-- url     : https://prove2.me/submissions/19e8993a-7b6a-45e7-bc20-1ac870b61a70

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable
import Theorems.Thm_AvramDividend_Classical_local_verification_candidate_borel_and_postPayment_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- No independently postulated measurability for the true source terminal. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (q : ℝ) (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :
    AEStronglyMeasurable Term P := by
  have hwMeas : Measurable w :=
    (local_verification_candidate_borel_and_postPayment_adapted
      X x D hD.1.1 w hw_cont hw_neg).1
  have hWMeas : Measurable W :=
    avram_wave6_06_original_ruin_piecewise_book_postpayment_terminal_measurable
      X x D hD.1.1 τ hτ W hW
  have hτReal : Measurable (fun ω : Ω => (τ ω : ℝ)) :=
    avram_wave6_06_original_rightcont_stopping_nnreal_real_measurable τ hτ
  have hDisc : Measurable (fun ω : Ω =>
      Real.exp (-(q * (τ ω : ℝ)))) :=
    (measurable_const.mul hτReal).neg.exp
  have hTermMeas : Measurable Term := by
    have heq : Term = (fun ω : Ω =>
        Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) :=
      funext hTerm
    rw [heq]
    exact hDisc.mul (hwMeas.comp hWMeas)
  exact hTermMeas.aestronglyMeasurable
