-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f6_gaussian_qscale_unchecked_existence
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:07:32.657775+00:00
-- url     : https://prove2.me/submissions/5515a44f-fbd8-4362-af17-ae8a6ed1fc98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_discount_scale_exists
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_scale_exists_from_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hσ : 0 < X.σ) :
    ∃ W : ℝ → ℝ, IsScaleFunction X q W := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hv
    have hzero : X.σ = 0 := hv.1
    exact (ne_of_gt hσ) hzero
  obtain ⟨W₀, hW₀⟩ :=
    avram_p4_f6_gaussian_zero_discount_scale_exists X hX hσ
  exact unbounded_positive_discount_scale_exists_from_zero
    X hnbv W₀ hW₀ q hq
