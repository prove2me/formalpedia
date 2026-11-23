-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x9.card_map_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:56:33.869749+00:00
-- url     : https://prove2.me/submissions/4f308fc1-c3d1-41cd-977e-42404c936ffa

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PadicChangeOfVariables

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x9
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
variable (π : Kˣ)
namespace Formalism.FourierDecayAlt.P.A6x9
theorem _root_.solution (L : AddSubgroup K) :
    Nat.card (L.map (QuotientAddGroup.mk' R.toAddSubgroup)) = R.toAddSubgroup.relIndex L := by
  rw [← AddSubgroup.relIndex_bot_left, ← AddSubgroup.relIndex_comap, AddMonoidHom.comap_bot,
    QuotientAddGroup.ker_mk']
end Formalism.FourierDecayAlt.P.A6x9
