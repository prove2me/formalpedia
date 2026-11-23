-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.Near.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:43.956823+00:00
-- url     : https://prove2.me/submissions/0314abf3-d278-437d-a503-4866aad3b321

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_near_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Near_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
namespace Near
theorem _root_.solution {a x : K} (ha : a ∈ R) (hx : Near R a x) (n : ℕ) : Near R a (x ^ n) := by
  induction n with
  | zero => simpa using near_one a
  | succ n ih => rw [pow_succ]; exact ih.mul ha hx
end Near
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
