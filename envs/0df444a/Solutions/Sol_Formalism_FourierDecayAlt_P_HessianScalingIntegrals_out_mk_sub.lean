-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HessianScalingIntegrals.out_mk_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:18.064593+00:00
-- url     : https://prove2.me/submissions/fa1e7dba-75b8-484e-bba7-123801b63cb5

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HessianScalingIntegrals

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HessianScalingIntegrals
variable {K : Type} [CommRing K]
namespace Formalism.FourierDecayAlt.P.HessianScalingIntegrals
theorem _root_.solution (Λ : AddSubgroup K) (x : K) :
    (Quotient.out (x : K ⧸ Λ) : K) - x ∈ Λ := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add Λ x
  rw [hh]; simp
end Formalism.FourierDecayAlt.P.HessianScalingIntegrals
