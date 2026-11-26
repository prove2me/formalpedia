-- Prove2me | solution 1 for CurveScaledEvalMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:52:46.449295+00:00
-- url     : https://prove2.me/submissions/5959b7ba-79b5-4861-814e-72456bd9d58d

import Definitions.Def_Tablet_CurveEvalJointMeasurable
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveScaledEvalMeasurable
import Theorems.Thm_CurveEvalJointMeasurable
import Theorems.Thm_CurveLenMeasurable


set_option autoImplicit false

theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) : Measurable (fun γ : Curve E => γ.toFun (c * γ.len)) := by
-- BODY
  exact CurveEvalJointMeasurable.comp
    ((measurable_const.mul CurveLenMeasurable).prodMk measurable_id)
