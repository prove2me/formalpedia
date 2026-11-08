-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_family_discounted_terminal_uniform_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:47:59.122466+00:00
-- url     : https://prove2.me/submissions/55976ef5-22fe-4da1-b516-2a1f25ed3917

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_stopping_family_uniform_terminal_bound

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
    (σ : ℕ → Ω → ℝ≥0) (W Term : ℕ → Ω → ℝ)
    (hW : ∀ k ω, W k ω =
      if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
      else riskProcess X x D (σ k ω) ω)
    (q : ℝ) (hq : 0 ≤ q)
    (hTerm : ∀ k ω, Term k ω =
      Real.exp (-(q * (σ k ω : ℝ))) * w (W k ω))
    (hTermMeas : ∀ k, AEStronglyMeasurable (Term k) P) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ k ω, |Term k ω| ≤ B) ∧
      (∀ k, Integrable (Term k) P) := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨B, hB, hwb⟩ :=
    avram_ubv_finite9_original_stopping_family_uniform_terminal_bound
      X x C hfinite hxc w hw_cont hw_neg D hD σ W hW
  have hbound : ∀ k ω, |Term k ω| ≤ B := by
    intro k ω
    have ht : 0 ≤ (σ k ω : ℝ) := (σ k ω).property
    have hp : 0 ≤ q * (σ k ω : ℝ) := mul_nonneg hq ht
    have hexp : 0 ≤ Real.exp (-(q * (σ k ω : ℝ))) :=
      Real.exp_nonneg _
    have hexp1 : Real.exp (-(q * (σ k ω : ℝ))) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      linarith
    calc
      |Term k ω| =
          Real.exp (-(q * (σ k ω : ℝ))) * |w (W k ω)| := by
            rw [hTerm k ω, abs_mul, abs_of_nonneg hexp]
      _ ≤ |w (W k ω)| := by
            nlinarith [abs_nonneg (w (W k ω))]
      _ ≤ B := hwb k ω
  refine ⟨B, hB, hbound, ?_⟩
  intro k
  apply MeasureTheory.Integrable.of_bound (hTermMeas k) B
  exact Filter.Eventually.of_forall (fun ω => by
    simpa only [Real.norm_eq_abs] using hbound k ω)
