-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.TA1.ls_ext
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:56.70802+00:00
-- url     : https://prove2.me/submissions/d9c57fac-978c-4afe-a677-55b16045eb1e

import Definitions.Def_Formalism_HermitianCurvature_StatementTA
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagonalTopBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.TA1
open Formalism.FourierDecayAlt.TA Finset Filter Topology
open scoped InnerProductSpace ComplexConjugate
variable {E : Type} [DecidableEq E]
omit [DecidableEq E]
namespace Formalism.FourierDecayAlt.P.TA1
theorem _root_.solution (h : Pt E) (s : ℕ) (t : E) : ls (Formalism.FourierDecayAlt.TA.ext h s t) = s := by
  simp [ls, Formalism.FourierDecayAlt.TA.ext]
end Formalism.FourierDecayAlt.P.TA1
