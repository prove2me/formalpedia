-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_deriv_lower_of_unit_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:03:22.909503+00:00
-- url     : https://prove2.me/submissions/5f825745-129f-4093-bbc1-996dc516f04d

import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_boundary_reward_of_unit_gap
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The source Stieltjes barrier reward bound forces a quantitative
positive derivative lower bound at every differentiability point. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ a : ℝ, 0 < a →
      c * W (a + 1) ≤ W (a + 1) - W a) :
    ∀ a : ℝ, 0 < a → DifferentiableAt ℝ W a →
      c * W a ≤ deriv W a := by
  intro a ha hdiff
  have hderiv : 0 < deriv W a :=
    avram_wave3_02_deriv_pos_of_pointwise_diff
      X hX q hq W hW a ha hdiff
  have hratio : W a / deriv W a ≤ 1 / c := by
    apply (ENNReal.ofReal_le_ofReal_iff
      (le_of_lt (div_pos one_pos hc))).mp
    calc
      ENNReal.ofReal (W a / deriv W a) =
          barrierSupValue X a q :=
        (avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
          X hX q hq W hW a ha hdiff).symm
      _ ≤ ENNReal.ofReal (1 / c) :=
        avram_wave3_02_uniform_boundary_reward_of_unit_gap
          X hX q hq W hW c hc hgap a (le_of_lt ha)
  have hh : W a * c ≤ 1 * deriv W a :=
    (div_le_div_iff₀ hderiv hc).mp hratio
  calc
    c * W a = W a * c := mul_comm _ _
    _ ≤ 1 * deriv W a := hh
    _ = deriv W a := one_mul _
