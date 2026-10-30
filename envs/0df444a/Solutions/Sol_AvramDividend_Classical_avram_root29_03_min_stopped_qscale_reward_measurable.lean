-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_03_min_stopped_qscale_reward_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:02:41.30099+00:00
-- url     : https://prove2.me/submissions/31576195-97e9-40a9-8daf-016f7372195f

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_both_named_passage_clocks_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_scaleFunction_measurable_of_punctured_continuity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- The actual discounted q-scale terminal reward at the two-sided
minimum exit clock is measurable, including the infinite-clock value.
No variation, Standing or killed stochastic identity is assumed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) :
    Measurable (fun ω : Ω =>
      ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω))))) *
      ENNReal.ofReal (W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω))) := by
  have hBoth :=
    chat03_both_named_passage_clocks_measurable X (-x) (a - x)
  have hClock : Measurable (fun ω : Ω => min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)) :=
    hBoth.1.min hBoth.2
  have hTime : Measurable (fun ω : Ω => (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal) := by
    measurability
  have hState :
      Measurable (fun ω : Ω => X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω) :=
    (chat04_levy_joint_time_state_measurable X).comp
      (hTime.prodMk measurable_id)
  have hScale : Measurable W :=
    chat04_scaleFunction_measurable_of_punctured_continuity X q W hW
  have hScaleAt :
      Measurable (fun ω : Ω => W (x + X.X (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)).toNNReal ω)) :=
    hScale.comp (measurable_const.add hState)
  have hDiscount :
      Measurable (fun ω : Ω =>
        ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal (min (twoSidedExitUpTime X (a - x) ω) (twoSidedExitDownTime X (-x) ω)))))) := by
    measurability
  exact hDiscount.mul (ENNReal.measurable_ofReal.comp hScaleAt)
