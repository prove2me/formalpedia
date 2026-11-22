-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.mem_Pk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:41:40.408808+00:00
-- url     : https://prove2.me/submissions/3c90a74a-3f9a-4b6c-8c07-8de92dc035a8

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HenselRootsBounded
variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution {k : ℤ} {x : K} : x ∈ Pk R ϖ k ↔ ((ϖ ^ (-k) : Kˣ) : K) * x ∈ R := Iff.rfl
end Formalism.FourierDecayAlt.P.HenselRootsBounded
