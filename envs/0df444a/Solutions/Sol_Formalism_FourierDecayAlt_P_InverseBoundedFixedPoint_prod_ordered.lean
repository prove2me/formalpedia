-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.prod_ordered
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:54.012879+00:00
-- url     : https://prove2.me/submissions/a03ac651-e734-4f71-aa47-cdb50dc0ce7c

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] {m : ℕ}
namespace Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
theorem _root_.solution (y w : Fin m → K) (h : ∀ k, (1 + y k) * w k = 1) (s : Finset (Fin m)) :
    ∏ i ∈ s, w i = 1 - ∑ i ∈ s, (y i * w i) * ∏ j ∈ s.filter (· < i), w j := by
  have ha : ∀ k, 1 - y k * w k = w k := fun k => by linear_combination -h k
  have := Finset.prod_one_sub_ordered s (fun i => y i * w i)
  simpa only [ha] using this
end Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
