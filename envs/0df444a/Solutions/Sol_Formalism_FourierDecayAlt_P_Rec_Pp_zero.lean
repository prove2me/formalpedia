-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Rec.Pp_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:02:18.913427+00:00
-- url     : https://prove2.me/submissions/92758143-6af4-40b5-af45-f6a0c09cbd8c

import Definitions.Def_Formalism_HermitianCurvature_Statement
import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SharpRecursion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Rec
open Finset Real
namespace Formalism.FourierDecayAlt.P.Rec
theorem _root_.solution (e : ℕ → ℝ) : Pp e 0 = 1 := by
  simp [Pp]
end Formalism.FourierDecayAlt.P.Rec
