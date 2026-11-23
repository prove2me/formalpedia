-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.conjS_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:49.090198+00:00
-- url     : https://prove2.me/submissions/14429db7-7825-4310-8985-39d6bc26c5ac

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_MeasIterDeriv
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeightedL2BoundedMul
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_A3_dS_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_LEx2_dS_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx2
theorem _root_.solution (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) : conjS B T u 0 = T u := by
  have h0 := dS_zero B T u
  funext ω a
  have h := congrFun (congrFun h0 ω) a
  simpa [dS] using h
end Formalism.FourierDecayAlt.P.LEx2
