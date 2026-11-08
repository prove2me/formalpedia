-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_discounted_terminal_family_allLp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T10:20:37.506354+00:00
-- url     : https://prove2.me/submissions/3f08f993-75e6-46a9-acbd-3a55bc591e7a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_family_discounted_terminal_uniform_L1

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-- Every original finite-cap stopped terminal localisation is in all Lp spaces. -/
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
    ∀ p : ℝ≥0∞, ∀ k : ℕ, MemLp (Term k) p P  := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨B, hB, hBound, _⟩ :=
    avram_ubv_finite9_original_family_discounted_terminal_uniform_L1
      X x C hfinite hxc w hw_cont hw_neg D hD σ W Term hW q hq hTerm hTermMeas
  intro p k
  apply MeasureTheory.MemLp.of_bound (hTermMeas k) B
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs] using hBound k ω
