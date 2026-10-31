-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_uniform_boundary_reward_of_unit_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T12:35:39.704807+00:00
-- url     : https://prove2.me/submissions/4c8d0e9e-2a77-4254-919b-5a4eed10f032

import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_positive_gap_upper_value
import Theorems.Thm_AvramDividend_Classical_barrierSupValue_mono_barrier
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A barrier-independent positive one-step scale gap bounds every actual
reflected-regulator Stieltjes dividend reward by one common finite constant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ a : ℝ, 0 < a →
      c * W (a + 1) ≤ W (a + 1) - W a) :
    ∀ a : ℝ, 0 ≤ a →
      barrierSupValue X a q ≤ ENNReal.ofReal (1 / c) := by
  have hpos : ∀ a : ℝ, 0 < a →
      barrierSupValue X a q ≤ ENNReal.ofReal (1 / c) := by
    intro a ha
    have ha1 : 0 < a + 1 := by linarith
    have hWa1 : 0 < W (a + 1) :=
      scaleFunction_strict_pos_of_standing X hX q hq W hW (a + 1) ha1
    have hWa : 0 < W a :=
      scaleFunction_strict_pos_of_standing X hX q hq W hW a ha
    have hstep : c * W (a + 1) ≤ W (a + 1) - W a :=
      hgap a ha
    have hgap_pos : 0 < W (a + 1) - W a :=
      lt_of_lt_of_le (mul_pos hc hWa1) hstep
    have hinc : W a < W (a + 1) := sub_pos.mp hgap_pos
    have hupper :=
      avram_wave3_02_positive_gap_upper_value
        X hX q hq W hW a 1 ha one_pos hWa1 (le_of_lt hWa) hinc
    have hdiv : W (a + 1) / (W (a + 1) - W a) ≤ 1 / c := by
      apply (div_le_div_iff₀ hgap_pos hc).2
      simpa only [mul_one, one_mul, mul_comm] using hstep
    exact le_trans (by simpa only [one_mul] using hupper)
      (ENNReal.ofReal_le_ofReal hdiv)
  intro a ha
  rcases eq_or_lt_of_le ha with hz | hpositive
  · subst a
    exact le_trans
      (barrierSupValue_mono_barrier X 0 1 q (by norm_num))
      (hpos 1 (by norm_num))
  · exact hpos a hpositive
