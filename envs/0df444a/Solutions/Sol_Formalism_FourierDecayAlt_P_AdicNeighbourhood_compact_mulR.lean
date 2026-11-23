-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.AdicNeighbourhood.compact_mulR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:54.907598+00:00
-- url     : https://prove2.me/submissions/4a0bc9ce-2ea4-4ccf-84fe-ee99bc2cbf0f

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_I_compact
import Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_mem_mulR

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
theorem _root_.solution [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
    (hc : IsCompact (R : Set K)) (ν : K) : IsCompact ((mulR R ν : AddSubgroup K) : Set K) := by
  have : ((mulR R ν : AddSubgroup K) : Set K) = I R ν := by
    ext x; exact mem_mulR
  rw [this]; exact I_compact hc ν
end Formalism.FourierDecayAlt.P.AdicNeighbourhood
