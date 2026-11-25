-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliCoordinates.Sup.smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:19:47.100898+00:00
-- url     : https://prove2.me/submissions/53cbf1af-e417-498d-9b7d-0c28fe62bfa2

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.CapelliCoordinates
variable {k r : ℕ} {i : Fin (r + 1)}
namespace Formalism.FourierDecayAlt.P.CapelliCoordinates
namespace Sup
theorem _root_.solution {Z : Mx k r} (hZ : Sup k r i Z) (c : ℂ) : Sup k r i (c • Z) := fun p hp => by
  obtain ⟨h1, h2⟩ := hZ p hp
  refine ⟨by rw [Matrix.smul_mulVec, h1, smul_zero], ?_⟩
  rw [conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mulVec, h2, smul_zero]
end Sup
end Formalism.FourierDecayAlt.P.CapelliCoordinates
