-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_original_strict_survival_preterminal_nonnegative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T13:14:58.296859+00:00
-- url     : https://prove2.me/submissions/8bdae9df-7928-4e29-8b1e-29d4bb39288f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
/-- Nonnegativity of the actual original strictly surviving
    pre-rightpayment terminal, keeping S at its NNReal source type. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (w : ℝ → ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (hT : 0 ≤ T) (hTpos : 0 < T)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) :
    let S : ℝ≥0 := ⟨T, hT⟩
    ∀ ω, 0 ≤
      (if (S : ℝ≥0∞) < ruinTime X x D ω then
        Real.exp (-(q * T)) * w (riskProcess X x D S ω)
      else 0) := by
  dsimp
  intro ω
  split_ifs with hsurv
  · exact mul_nonneg (Real.exp_nonneg _) (hw_nonneg ω ⟨T, hT⟩ (by
      exact_mod_cast hTpos) hsurv)
  · exact le_refl 0
