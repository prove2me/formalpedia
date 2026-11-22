-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A6x4.isLat_mulR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:17.841987+00:00
-- url     : https://prove2.me/submissions/f434049c-a568-4249-8432-dd8e74f40bd2

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ModulusLocallyConstant
import Theorems.Thm_Formalism_FourierDecayAlt_P_A6x4_mem_mulR_iff

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
theorem _root_.solution (hD : LocalDatum K R ψ) {a b : K} (hab : a * b = 1) : IsLat (mulR R a) := by
  constructor
  · have : ((mulR R a : AddSubgroup K) : Set K) = (fun x => b * x) ⁻¹' (R : Set K) := by
      ext x
      exact mem_mulR_iff hab x
    rw [this]
    exact hD.isOpen.preimage (by fun_prop)
  · have : ((mulR R a : AddSubgroup K) : Set K) = (fun x => a * x) '' (R : Set K) := by
      unfold mulR
      rw [AddSubgroup.coe_map]
      rfl
    rw [this]
    exact hD.isCompact.image (by fun_prop)
end Formalism.FourierDecayAlt.P.A6x4
