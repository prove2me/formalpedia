-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.LEx1.ld_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:23:42.765092+00:00
-- url     : https://prove2.me/submissions/5e04d6aa-5e0a-4968-b463-5bfe8e72ce6c

import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaEprimeFromSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.LEx1
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset
open scoped ComplexConjugate
namespace Formalism.FourierDecayAlt.P.LEx1
theorem _root_.solution (q : ℕ) (x : ℝ) : ld q (fun _ => (1:ℝ)) x = if q = 0 then 1 else 0 := by
  unfold ld
  cases q with
  | zero => simp
  | succ n => simp [iteratedDeriv_succ']
end Formalism.FourierDecayAlt.P.LEx1
