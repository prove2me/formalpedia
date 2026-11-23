-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Mx2.coord_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:11.059442+00:00
-- url     : https://prove2.me/submissions/f6923500-8081-4db4-a729-d7044a4bc4bb

import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelNablaStarRelations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Finset
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Mx2
namespace Formalism.FourierDecayAlt.P.Mx2
theorem _root_.solution (r : ℕ) (v : Var r) : coord v ≠ 0 := by
  simp [coord]
end Formalism.FourierDecayAlt.P.Mx2
