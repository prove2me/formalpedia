-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HessianScalingIntegrals.ball_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:17.329421+00:00
-- url     : https://prove2.me/submissions/6b5b7c5e-990a-4b18-b3e1-ee47e4f75313

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
theorem _root_.solution (B : AddSubgroup K) {m : ℕ} (x l : Fin m → K) (z : K) (hl : ∀ k, l k ∈ B) :
    (∀ k, (x + l) k - z ∈ B) ↔ ∀ k, x k - z ∈ B := by
  refine forall_congr' fun k => ?_
  have h1 : (x + l) k - z = x k - z + l k := by simp only [Pi.add_apply]; ring
  rw [h1]
  exact B.add_mem_cancel_right (hl k)
end Formalism.FourierDecayAlt.P.HessianScalingIntegrals
