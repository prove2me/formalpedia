-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_standing_barrierSupValue_pos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:46:40.544802+00:00
-- url     : https://prove2.me/submissions/b647319c-d99e-4461-a026-842103182397

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_scale_strictMonoOn_positive
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_left_step_lower
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The source killed reflected-regulator reward is strictly positive at
positive barriers under Standing, independently of scale differentiability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) :
    0 < barrierSupValue X a q := by
  have hhalf : 0 < a / 2 := by linarith
  have hhalflt : a / 2 < a := by linarith
  have hleftarg : 0 < a - a / 2 := by linarith
  have hWleft : 0 < W (a - a / 2) :=
    scaleFunction_strict_pos_of_standing
      X hX q hq W hW (a - a / 2) hleftarg
  have hWinc : W (a - a / 2) < W a :=
    (avram_wave3_02_scale_strictMonoOn_positive X hX q hq W hW)
      (Set.mem_Ioi.mpr hleftarg) (Set.mem_Ioi.mpr ha) (by linarith)
  have hratio :
      0 < (a / 2) * W (a - a / 2) / (W a - W (a - a / 2)) :=
    div_pos (mul_pos hhalf hWleft) (sub_pos.mpr hWinc)
  have hLo :=
    avram_wave3_02_standing_left_step_lower
      X hX q hq W hW a (a / 2) ha hhalf hhalflt
  exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hratio) hLo
