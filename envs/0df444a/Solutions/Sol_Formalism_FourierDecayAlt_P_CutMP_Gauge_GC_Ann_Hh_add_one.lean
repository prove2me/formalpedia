-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.Hh_add_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:51.950507+00:00
-- url     : https://prove2.me/submissions/ab578faf-b4f2-4e32-9139-6091bc779687

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ImCircleIntegral
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThShiftInt
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_Hh_add_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex MeasureTheory intervalIntegral
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {TT : ℝ} {α : ℂ → ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution {w : ℂ} (hw : w ∈ Hh TT) : w + 2 * Real.pi * I ∈ Hh TT := by
  have := (Hh_add_int (TT := TT) (w := w) 1).2 hw
  simpa using this
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
