-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.mulQ_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:59.449658+00:00
-- url     : https://prove2.me/submissions/f9ef8d21-45f0-4615-91a7-a98f4c562656

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
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution (R : Subring K) (lam : Kˣ) (h1 : (lam : K) ∈ R) (h2 : ((lam⁻¹ : Kˣ) : K) ∈ R)
    (x : K) : mulQ R lam h1 h2 (x : K ⧸ R.toAddSubgroup) =
      (((lam : K) * x : K) : K ⧸ R.toAddSubgroup) := rfl
end Formalism.FourierDecayAlt.P.HenselRootsBounded
