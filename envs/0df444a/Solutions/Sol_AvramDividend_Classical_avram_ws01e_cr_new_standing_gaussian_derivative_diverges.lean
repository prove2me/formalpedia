-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_cr_new_standing_gaussian_derivative_diverges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T00:42:26.066037+00:00
-- url     : https://prove2.me/submissions/3a851d84-104a-4922-8316-76894273817c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_c1_derivative_growth_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop_of_eventually_ge_exp

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

/-- The Gaussian q-scale derivative diverges at infinity under classical
    standing hypotheses, with C¹ supplied by genuine Gaussian smoothing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
    Tendsto (deriv W) atTop atTop := by
  have hreg : ContDiffOn ℝ 1 W (Ioi 0) :=
    scaleFunction_contDiff_one_gaussian_without_standing
      X q hq W hW hσ
  have hgrowth : ∃ φ c : ℝ, 0 < φ ∧ 0 < c ∧
      ∀ᶠ x in Filter.atTop,
        c * Real.exp (φ * x) ≤ deriv W x :=
    avram_ws01e_cr_new_c1_derivative_growth_of_standing
      X hX q hq W hW hreg
  exact scaleDeriv_tendsto_atTop_of_eventually_ge_exp
    X hX q hq W hW hgrowth
