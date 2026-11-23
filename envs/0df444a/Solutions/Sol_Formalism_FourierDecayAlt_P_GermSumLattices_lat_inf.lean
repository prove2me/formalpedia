-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.GermSumLattices.lat_inf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:44:50.543495+00:00
-- url     : https://prove2.me/submissions/8015f2de-afd2-4a4a-bd5c-19aec5e5651b

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
namespace Formalism.FourierDecayAlt.P.GermSumLattices
theorem _root_.solution {L M : AddSubgroup K} (hL : IsLat L) (hM : IsOpen (M : Set K)) :
    IsLat (L ⊓ M) := by
  refine ⟨by rw [AddSubgroup.coe_inf]; exact hL.1.inter hM, ?_⟩
  rw [AddSubgroup.coe_inf]
  exact hL.2.inter_right (AddSubgroup.isClosed_of_isOpen M hM)
end Formalism.FourierDecayAlt.P.GermSumLattices
