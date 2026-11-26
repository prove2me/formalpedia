-- Prove2me | solution 1 for CurveRestrictTotMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:53:08.603506+00:00
-- url     : https://prove2.me/submissions/516b7198-7506-4240-981b-a6e06d7c1fc0

import Definitions.Def_Tablet_curveRestrictTot
import Definitions.Def_Tablet_CurveMeasurableSpace
import Definitions.Def_Tablet_CurveEvalJointMeasurable
import Definitions.Def_Tablet_CurveLenMeasurable
import Definitions.Def_Tablet_CurveRestrictTotMeasurable
import Theorems.Thm_CurveEvalJointMeasurable
import Theorems.Thm_CurveLenMeasurable


set_option autoImplicit false

theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (a b : ℝ) : Measurable (fun γ : Curve E => curveRestrictTot γ a b) := by
-- BODY
  -- Universal property of the evaluation comap sigma-algebra on `Curve E`.
  have into_curve : ∀ f : Curve E → Curve E,
      Measurable (fun x => ((f x).len, (f x).toFun)) → Measurable f := by
    intro f h
    refine measurable_iff_comap_le.mpr ?_
    show MeasurableSpace.comap f
        (MeasurableSpace.comap (fun γ : Curve E => (γ.len, γ.toFun)) inferInstance) ≤ _
    rw [MeasurableSpace.comap_comp]
    exact measurable_iff_comap_le.mp h
  have hlen : Measurable (fun γ : Curve E => γ.len) := CurveLenMeasurable
  have ha' : Measurable (fun γ : Curve E => min (max a 0) γ.len) := measurable_const.min hlen
  have hb' : Measurable (fun γ : Curve E =>
      max (min (max a 0) γ.len) (min (max b 0) γ.len)) :=
    ha'.max (measurable_const.min hlen)
  refine into_curve _ ?_
  refine Measurable.prodMk ?_ ?_
  · exact hb'.sub ha'
  · refine measurable_pi_lambda _ (fun u => ?_)
    exact CurveEvalJointMeasurable.comp
      ((ha'.add ((hb'.sub ha').min measurable_const)).prodMk measurable_id)
