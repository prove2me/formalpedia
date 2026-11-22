-- Prove2me | solution 5 for AvramDividend.Classical.avram_p4_f6_positive_gaussian_qscale_exists
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:35:10.46343+00:00
-- url     : https://prove2.me/submissions/9b16f154-9236-4173-9df1-97dee1823af1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_p4_f6_gaussian_zero_discount_scale_exists
import Theorems.Thm_AvramDividend_Classical_unbounded_positive_discount_scale_exists_from_zero
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_unbounded
set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hσ : 0 < X.σ) :
    ∃ W : ℝ → ℝ, IsScaleFunction X q W ∧ 0 < W 1  := by
  have hnbv : ¬ X.BoundedVariation := by
    intro hBV
    have hσzero : X.σ = 0 := hBV.1
    linarith
  obtain ⟨W₀, hW₀⟩ :=
    avram_p4_f6_gaussian_zero_discount_scale_exists X hX hσ
  obtain ⟨Wq, hWq⟩ :=
    unbounded_positive_discount_scale_exists_from_zero
      X hnbv W₀ hW₀ q hq
  refine ⟨Wq, hWq, ?_⟩
  exact scaleFunction_strict_pos_of_unbounded
    X q Wq hWq hnbv 1 (by norm_num)
