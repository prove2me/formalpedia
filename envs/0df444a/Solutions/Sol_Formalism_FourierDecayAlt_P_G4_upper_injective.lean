-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.G4.upper_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:43:40.35114+00:00
-- url     : https://prove2.me/submissions/16090902-8cbd-4401-ba9a-29c2f78220de

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerBlockPoint

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open Formalism.FourierDecayAlt.G
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.G4
namespace Formalism.FourierDecayAlt.P.G4
theorem _root_.solution {d : ℕ} {v v' : UT d → ℂ} (h : upper v = upper v') : v = v' := by
  ext ⟨⟨i, j⟩, hij⟩
  have hij' : i < j := hij
  have := congrFun (congrFun h i) j
  simpa [upper, strictUpper, hij', hij'.ne] using this
end Formalism.FourierDecayAlt.P.G4
