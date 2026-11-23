-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HessianScalingIntegrals.psi_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:18.349388+00:00
-- url     : https://prove2.me/submissions/7df70654-9036-494d-99cd-5b0ddb476691

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
theorem _root_.solution (ψ : AddChar K ℂ) (a : K) : ψ a ≠ 0 := by
  intro h
  have h1 : ψ (a + -a) = 1 := by simp
  rw [AddChar.map_add_eq_mul, h, zero_mul] at h1
  exact zero_ne_one h1
end Formalism.FourierDecayAlt.P.HessianScalingIntegrals
