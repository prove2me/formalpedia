-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.hessian_at_critical
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:00:56.524037+00:00
-- url     : https://prove2.me/submissions/bebc6188-6db1-43e6-be81-5db8d9fc1a41

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhaseFunctionCriticalPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.G Formalism.FourierDecayAlt.P.G1
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.G.HessCrit := by
  intro m z hz
  ext i j
  by_cases h : i = j
  · subst h; simp [hess]; field_simp; ring
  · simp [hess, h]; field_simp; ring
end Formalism.FourierDecayAlt.P
