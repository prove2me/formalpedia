-- Prove2me | solution 2 for AvramDividend.Classical.scaleFunction_derivRightLimit_at_zero_eq_two_over_sigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:07:07.18299+00:00
-- url     : https://prove2.me/submissions/a4091437-01e4-4b09-939c-0ee6fc92684d

import Mathlib.Topology.NhdsWithin
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_scale_right_derivative_of_positive_esscher_root
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

/-- The q-scale's Gaussian derivative has right-hand limit 2/σ² at zero. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hzero : W 0 = 0)
    (hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt W (deriv W x) x) :
    Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 (2 / X.σ ^ 2)) := by
  obtain ⟨φ, hφ, hroot⟩ := positive_esscher_root_of_gaussian X q hq hσ
  exact gaussian_scale_right_derivative_of_positive_esscher_root
    X q hq W hW hσ φ hφ hroot
