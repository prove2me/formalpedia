-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.psi_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:19.663743+00:00
-- url     : https://prove2.me/submissions/460c9fb3-b7b5-4b1c-8b74-af478abb605b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.A6x4
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
namespace Formalism.FourierDecayAlt.P.A6x4
theorem _root_.solution (hD : LocalDatum K R ψ) {r : K} (hr : r ∈ R) : ψ r = 1 := by
  have := (hD.selfDual 1).2 R.one_mem r hr
  rwa [one_mul] at this
end Formalism.FourierDecayAlt.P.A6x4
