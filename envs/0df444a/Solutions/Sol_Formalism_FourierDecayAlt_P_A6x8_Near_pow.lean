-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x8.Near.pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:32:22.496976+00:00
-- url     : https://prove2.me/submissions/ae5ee2bd-3af0-448c-8236-18b3372bbb68

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_near_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Near_mul

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.A6x8
namespace Near
theorem _root_.solution {a x : K} (ha : a ∈ R) (hx : Near R a x) (n : ℕ) : Near R a (x ^ n) := by
  induction n with
  | zero => simpa using near_one a
  | succ n ih => rw [pow_succ]; exact ih.mul ha hx
end Near
end Formalism.FourierDecayAlt.P.A6x8
