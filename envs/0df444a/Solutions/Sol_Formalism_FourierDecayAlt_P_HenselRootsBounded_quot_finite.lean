-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HenselRootsBounded.quot_finite
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:13:59.638908+00:00
-- url     : https://prove2.me/submissions/43d8f0eb-c3c9-4b14-95fc-7205805be457

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HenselRootsBounded
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_isOpen
import Theorems.Thm_Formalism_FourierDecayAlt_P_HenselRootsBounded_Pk_isCompact

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
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
  {R : Subring K} {ϖ : Kˣ}
namespace Formalism.FourierDecayAlt.P.HenselRootsBounded
theorem _root_.solution (h : Ctx K R ϖ) (k l : ℤ) :
    Finite (Pk R ϖ k ⧸ (Pk R ϖ l).addSubgroupOf (Pk R ϖ k)) := by
  have : CompactSpace (Pk R ϖ k) := isCompact_iff_compactSpace.mp (Pk_isCompact h k)
  exact AddSubgroup.quotient_finite_of_isOpen _ ((Pk_isOpen h l).preimage continuous_subtype_val)
end Formalism.FourierDecayAlt.P.HenselRootsBounded
