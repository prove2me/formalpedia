-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx2.thetaRange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:25:55.333183+00:00
-- url     : https://prove2.me/submissions/f2c3e97c-f73e-43a2-987a-9a8ea1250f39

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ThetaLimit

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
theorem _root_.solution : ThetaRange := by
  intro ε σ x hε hσ hx
  unfold th
  have h0 : 0 < x / (x + ε) := by positivity
  have h1 : x / (x + ε) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  exact ⟨Real.rpow_pos_of_pos h0 σ, Real.rpow_le_one h0.le h1 hσ⟩
end Formalism.FourierDecayAlt.P.LEx2
