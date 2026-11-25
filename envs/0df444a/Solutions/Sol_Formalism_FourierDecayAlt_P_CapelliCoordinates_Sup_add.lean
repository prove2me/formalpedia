-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliCoordinates.Sup.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:38:24.102427+00:00
-- url     : https://prove2.me/submissions/4e948d73-66e9-4b0b-b9be-0a80a65ce71c

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
theorem _root_.solution {Z W : Mx k r} (hZ : Sup k r i Z) (hW : Sup k r i W) : Sup k r i (Z + W) := fun p hp => by
  obtain ⟨h1, h2⟩ := hZ p hp
  obtain ⟨h3, h4⟩ := hW p hp
  refine ⟨by rw [Matrix.add_mulVec, h1, h3, add_zero], ?_⟩
  rw [conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec, h2, h4, add_zero]
end Sup
end Formalism.FourierDecayAlt.P.CapelliCoordinates
