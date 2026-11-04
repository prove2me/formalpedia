-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f_assembly_original_any_index_rightjump_residual_tsum_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:56:57.62532+00:00
-- url     : https://prove2.me/submissions/24cf28f7-16c6-4a7c-ba72-ce65e49e6d6f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Source right-dividend signed residuals sum nonpositively over any index type. -/
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
    (hsummable : Summable (fun k : ι =>
      Real.exp (-(q * (t k : ℝ))) *
        ((rightLimit D (t k) ω - D (t k) ω) +
          w (x + X.X (t k) ω - rightLimit D (t k) ω) -
          w (riskProcess X x D (t k) ω)))) :
    (∑' k : ι, Real.exp (-(q * (t k : ℝ))) *
      ((rightLimit D (t k) ω - D (t k) ω) +
        w (x + X.X (t k) ω - rightLimit D (t k) ω) -
        w (riskProcess X x D (t k) ω))) ≤ 0 := by
  apply tsum_nonpos
  intro k
  simpa using
    (avram_p4_d_dividend_original_rightjump_discounted_residual_nonpos
      X x D w q hjump (fun _ => t k) ω (hpre k))
