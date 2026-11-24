-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.X.two_sum
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:07.190386+00:00
-- url     : https://prove2.me/submissions/9b453d3f-d7df-4ab6-88da-34b2f8949c9b

import Definitions.Def_Formalism_HermitianCurvature_StatementX
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalingExponentIdentities

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Matrix
open Formalism.FourierDecayAlt.P.X
namespace Formalism.FourierDecayAlt.P.X
theorem _root_.solution (l : ℕ) : 2 * (∑ a ∈ Finset.range l, a) = l * (l - 1) := by
  rw [mul_comm, Finset.sum_range_id_mul_two]
end Formalism.FourierDecayAlt.P.X
