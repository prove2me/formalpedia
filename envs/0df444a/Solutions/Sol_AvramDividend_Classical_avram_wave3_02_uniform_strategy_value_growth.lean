-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_02_uniform_strategy_value_growth
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T13:22:24.476048+00:00
-- url     : https://prove2.me/submissions/890d4fda-b44a-4d3e-af32-040285108440

import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_uniform_boundary_reward
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_barrierValue_le_boundary
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_above_value_eq_initial_excess_sup
import Theorems.Thm_AvramDividend_Classical_barrierValue_self_eq_barrierSupValue
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Uniform source-faithful growth bound for every admissible barrier
strategy and all nonnegative initial reserves, including zero cap. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a x : ℝ), 0 ≤ a → 0 ≤ x →
      dividendValue X q x (barrierStrategy X x a) ≤
        ENNReal.ofReal x + ENNReal.ofReal C := by
  obtain ⟨C, hC, hbound⟩ :=
    avram_wave3_02_standing_uniform_boundary_reward X hX q hq W hW
  refine ⟨C, hC, ?_⟩
  intro a x ha hx
  by_cases hax : a < x
  · calc
      dividendValue X q x (barrierStrategy X x a) =
          ENNReal.ofReal (x - a) + barrierSupValue X a q :=
        avram_wave3_02_above_value_eq_initial_excess_sup X q a x ha hax
      _ ≤ ENNReal.ofReal x + ENNReal.ofReal C :=
        add_le_add (ENNReal.ofReal_le_ofReal (by linarith)) (hbound a ha)
  · have hxa : x ≤ a := le_of_not_gt hax
    have hle : dividendValue X q x (barrierStrategy X x a) ≤
        barrierSupValue X a q := by
      rcases eq_or_lt_of_le ha with hz | hpositive
      · subst a
        have hxzero : x = 0 := le_antisymm hxa hx
        subst x
        exact le_of_eq (barrierValue_self_eq_barrierSupValue X q 0)
      · exact avram_root29_05_barrierValue_le_boundary
          X hX q hq a x hpositive hx hxa
    calc
      dividendValue X q x (barrierStrategy X x a) ≤
          barrierSupValue X a q := hle
      _ ≤ ENNReal.ofReal C := hbound a ha
      _ ≤ ENNReal.ofReal x + ENNReal.ofReal C :=
        le_add_of_nonneg_left (by exact bot_le)
