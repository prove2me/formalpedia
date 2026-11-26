-- Prove2me | solution 1 for CurveLenMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:50:32.393828+00:00
-- url     : https://prove2.me/submissions/151ea5f4-282d-4934-9314-46f0be55e296

import Definitions.Def_Tablet_CurveMeasurableSpace
import Definitions.Def_Tablet_CurveLenMeasurable

set_option autoImplicit false

theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E] :
    Measurable (fun γ : Curve E => γ.len) := by
-- BODY
  have heval : Measurable (fun γ : Curve E => (γ.len, γ.toFun)) :=
    measurable_iff_comap_le.mpr le_rfl
  exact measurable_fst.comp heval
