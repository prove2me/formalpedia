-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_scale_generator_origin_normalization_from_right_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:30:05.303917+00:00
-- url     : https://prove2.me/submissions/ea6d2f2c-f286-44ba-a3bd-377ce092c83c

import Mathlib.Topology.NhdsWithin
import Mathlib.Tactic.FieldSimp
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_gaussian_scale_right_derivative_of_positive_esscher_root
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped Topology NNReal ENNReal

/-- The boundary factor in the weighted Gaussian generator transform is one. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (η : ℝ) (hη : Tendsto (deriv W) (𝓝[>] (0 : ℝ)) (𝓝 η)) :
    (X.σ ^ 2 / 2) * η = 1 := by
  obtain ⟨φ, hφ, hroot⟩ :=
    positive_esscher_root_of_gaussian X q hq hσ
  have hgaussian : Tendsto (deriv W) (𝓝[>] (0 : ℝ))
      (𝓝 (2 / X.σ ^ 2)) :=
    gaussian_scale_right_derivative_of_positive_esscher_root
      X q hq W hW hσ φ hφ hroot
  have heq : η = 2 / X.σ ^ 2 := tendsto_nhds_unique hη hgaussian
  rw [heq]
  have hne : X.σ ≠ 0 := ne_of_gt hσ
  field_simp
