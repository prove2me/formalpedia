-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.A.dS_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:24:32.167809+00:00
-- url     : https://prove2.me/submissions/78ef4e2a-d24b-471f-bb79-49f36f2d9141

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ShiftBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx2 Formalism.FourierDecayAlt.P.LEx2.A
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
noncomputable section
namespace Formalism.FourierDecayAlt.P.LEx2.A
theorem _root_.solution (B : Base) {A A' : Type} (T : Fn B A → Fn B A') (u : Fn B A) : dS B T u 0 = T u := by
  funext ω a
  have h : mulF B (fun _ : ℝ => (1:ℝ)) u = u := by funext ω a; simp [mulF]
  simp [dS, conjS, h]
end Formalism.FourierDecayAlt.P.LEx2.A
