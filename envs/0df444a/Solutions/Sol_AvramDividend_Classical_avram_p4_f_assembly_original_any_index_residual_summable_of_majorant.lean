-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_any_index_residual_summable_of_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:14:14.074904+00:00
-- url     : https://prove2.me/submissions/99461635-c5d8-4075-8982-8c4e4dfaa1a0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_any_index_rightjump_residual_tsum_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Actual right-dividend residuals are summable under a norm majorant. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (ω : Ω) (t : ι → ℝ≥0)
    (hpre : ∀ k, t k = 0 ∨ (t k : ℝ≥0∞) < ruinTime X x D ω)
    (b : ι → ℝ) (hbsum : Summable b)
    (hbound : ∀ k,
      ‖Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          w (x + X.X (t k) ω - rightLimit D (t k) ω) -
          w (riskProcess X x D (t k) ω))‖ ≤ b k) :
    Summable (fun k : ι =>
      Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          w (x + X.X (t k) ω - rightLimit D (t k) ω) -
          w (riskProcess X x D (t k) ω))) ∧
    (∑' k : ι, Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          w (x + X.X (t k) ω - rightLimit D (t k) ω) -
          w (riskProcess X x D (t k) ω))) ≤ 0 := by
  have hs : Summable (fun k : ι =>
      Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          w (x + X.X (t k) ω - rightLimit D (t k) ω) -
          w (riskProcess X x D (t k) ω))) :=
    hbsum.of_norm_bounded hbound
  exact ⟨hs,
    avram_p4_f_assembly_original_any_index_rightjump_residual_tsum_nonpos
      X x D w q hjump ω t hpre hs⟩
