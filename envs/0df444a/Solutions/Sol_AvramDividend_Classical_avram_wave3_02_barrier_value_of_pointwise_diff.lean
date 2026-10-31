-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_barrier_value_of_pointwise_diff
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:05:55.759728+00:00
-- url     : https://prove2.me/submissions/679d28be-ca16-45a6-8b6c-c9197243296c

import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_value_eq_exit_factor
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Exact original all-starting-capital barrier value at a barrier point
where its q-scale function is differentiable; no global C1 assumption. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (hda : DifferentiableAt ℝ W a) :
    dividendValue X q x (barrierStrategy X x a) =
      ENNReal.ofReal (W x / deriv W a) := by
  have hWa : 0 < W a :=
    scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
  have hDa : 0 < deriv W a :=
    avram_wave3_02_deriv_pos_of_pointwise_diff
      X hX q hq W hW a ha hda
  have hfac : (W x / W a) * (W a / deriv W a) =
      W x / deriv W a := by
    field_simp [ne_of_gt hWa, ne_of_gt hDa] <;> ring
  calc
    dividendValue X q x (barrierStrategy X x a) =
        ENNReal.ofReal (W x / W a) * barrierSupValue X a q :=
      barrierStrategy_value_eq_exit_factor X hX q hq W hW a ha x hx0 hxa
    _ = ENNReal.ofReal (W x / W a) *
        ENNReal.ofReal (W a / deriv W a) := by
      rw [avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
        X hX q hq W hW a ha hda]
    _ = ENNReal.ofReal ((W x / W a) * (W a / deriv W a)) := by
      have hp : 0 ≤ W a / deriv W a := le_of_lt (div_pos hWa hDa)
      calc
        ENNReal.ofReal (W x / W a) * ENNReal.ofReal (W a / deriv W a) =
            ENNReal.ofReal (W a / deriv W a) * ENNReal.ofReal (W x / W a) :=
          mul_comm _ _
        _ = ENNReal.ofReal ((W a / deriv W a) * (W x / W a)) :=
          (ENNReal.ofReal_mul hp).symm
        _ = ENNReal.ofReal ((W x / W a) * (W a / deriv W a)) :=
          congrArg ENNReal.ofReal (mul_comm _ _)
    _ = ENNReal.ofReal (W x / deriv W a) := by rw [hfac]
