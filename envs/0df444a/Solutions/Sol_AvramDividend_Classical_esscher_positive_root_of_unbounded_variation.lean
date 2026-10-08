-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_of_unbounded_variation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T23:39:59.684987+00:00
-- url     : https://prove2.me/submissions/d9ad8179-07a4-4047-adea-ce280a3b884f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_esscher_positive_root_of_infinite_small_jump
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Positive root for any source unbounded-variation process once ψ-continuity is known. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (hcont : ContinuousOn X.ψ (Ici (0 : ℝ))) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by
  have hzero : X.ψ 0 = 0 := levy_laplace_exponent_zero X
  rcases unbounded_variation_gaussian_or_infinite_small_jump_moment X hbv with hσ | hinf
  · exact esscher_positive_root_of_gaussian X q hq hσ hcont hzero
  · rcases lt_or_eq_of_le X.σ_nonneg with hσ | hσ
    · exact esscher_positive_root_of_gaussian X q hq hσ hcont hzero
    · exact esscher_positive_root_of_infinite_small_jump X hσ.symm hinf q hq hcont hzero
