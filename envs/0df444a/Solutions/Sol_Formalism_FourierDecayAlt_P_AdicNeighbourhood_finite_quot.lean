-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.finite_quot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:54.963398+00:00
-- url     : https://prove2.me/submissions/b81e3c70-91dd-44a0-9823-b4937d90a0d0

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood

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
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.AdicNeighbourhood
theorem _root_.solution [TopologicalSpace K] [IsTopologicalRing K] (N Λ : AddSubgroup K)
    (hN : IsCompact (N : Set K)) (hΛ : IsOpen (Λ : Set K)) : Finite (N ⧸ Λ.addSubgroupOf N) := by
  have : CompactSpace N := isCompact_iff_compactSpace.1 hN
  exact AddSubgroup.quotient_finite_of_isOpen _ (hΛ.preimage continuous_subtype_val)
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
