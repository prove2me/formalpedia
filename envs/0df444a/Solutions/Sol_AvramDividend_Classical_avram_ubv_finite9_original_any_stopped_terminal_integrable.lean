-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_any_stopped_terminal_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:10:36.164082+00:00
-- url     : https://prove2.me/submissions/bff82693-d7db-40b8-89c6-f967b2ed1264

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_piecewise_terminal_w_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (hxc : ENNReal.ofReal x ≤ C)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if σ ω = 0 ∨ (σ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ ω) ω - rightLimit D (σ ω) ω
      else riskProcess X x D (σ ω) ω)
    (q : ℝ) (hq : 0 ≤ q)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (σ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P) :
    Integrable Term P := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨B, hB, hwb⟩ :=
    avram_ubv_finite9_original_piecewise_terminal_w_uniform_bound
      X x C hfinite hxc w hw_cont hw_neg D hD σ W hW
  have hpoint : ∀ ω, ‖Term ω‖ ≤ B := by
    intro ω
    have ht : 0 ≤ (σ ω : ℝ) := (σ ω).property
    have hp : 0 ≤ q * (σ ω : ℝ) := mul_nonneg hq ht
    have hexp : 0 ≤ Real.exp (-(q * (σ ω : ℝ))) :=
      Real.exp_nonneg _
    have hexp1 : Real.exp (-(q * (σ ω : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      linarith
    calc
      ‖Term ω‖ =
          Real.exp (-(q * (σ ω : ℝ))) * |w (W ω)| := by
            rw [hTerm ω, Real.norm_eq_abs, abs_mul, abs_of_nonneg hexp]
      _ ≤ |w (W ω)| := by
            nlinarith [abs_nonneg (w (W ω))]
      _ ≤ B := hwb ω
  exact MeasureTheory.Integrable.of_bound hTermMeas B
    (Filter.Eventually.of_forall hpoint)
