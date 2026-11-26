-- Prove2me | solution 1 for CurveEvalJointMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:50:32.938673+00:00
-- url     : https://prove2.me/submissions/485994c4-8fee-499a-94f1-3cdd81b2753f

import Definitions.Def_Tablet_CurveMeasurableSpace
import Definitions.Def_Tablet_CurveLipschitz
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic
import Definitions.Def_Tablet_CurveEvalJointMeasurable
import Theorems.Thm_CurveLipschitz


set_option autoImplicit false
open MeasureTheory
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E] :
    Measurable (Function.uncurry (fun (t : ℝ) (γ : Curve E) => γ.toFun t)) := by
-- BODY
  have heval : Measurable (fun γ : Curve E => (γ.len, γ.toFun)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hpt : ∀ t : ℝ, Measurable (fun γ : Curve E => γ.toFun t) :=
    fun t => ((measurable_pi_apply t).comp measurable_snd).comp heval
  exact measurable_uncurry_of_continuous_of_measurable
    (fun γ => (CurveLipschitz γ).continuous) hpt
