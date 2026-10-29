-- Prove2me | solution 1 for AvramDividend.Classical.avram_ws01e_bf_new_bv_hjb_all_positive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T00:43:10.417572+00:00
-- url     : https://prove2.me/submissions/04199b2f-c5a4-4493-86fb-58f6fcf1c550

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_hjb_except_cstar
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_cstar_hjb_at_cap
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by
  intro y hy
  by_cases hyc : y = (cstar W).toReal
  · subst hyc
    obtain ⟨h1, -, h3⟩ := AvramDividend.Classical.avram_ws01e_bf_new_bv_cstar_hjb_at_cap X hX q hq W hW hbv hy
    exact ⟨h1, h3⟩
  · exact AvramDividend.Classical.avram_ws01e_bf_new_bv_hjb_except_cstar X hX q hq W hW hbv hgen y hy hyc
