-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.mulR_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:53:21.560597+00:00
-- url     : https://prove2.me/submissions/68e83278-c05f-4e29-85a6-3b3d86f749a9

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
theorem _root_.solution {z v w : K} (hvw : v * w = 1) (hv : v ∈ R) (hw : w ∈ R) :
    mulR R (z * v) = mulR R z := by
  ext y
  unfold mulR
  simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
  constructor
  · rintro ⟨r, hr, rfl⟩
    exact ⟨v * r, R.mul_mem hv hr, by ring⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨w * r, R.mul_mem hw hr, by linear_combination (z * r) * hvw⟩
end Formalism.FourierDecayAlt.P.A6x4
