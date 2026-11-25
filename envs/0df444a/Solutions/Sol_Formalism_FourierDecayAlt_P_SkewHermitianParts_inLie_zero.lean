-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SkewHermitianParts.inLie_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:37:48.772549+00:00
-- url     : https://prove2.me/submissions/de767123-6582-4474-b5c7-91a89b8918c0

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr Formalism.FourierDecayAlt.P.QrD
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.SkewHermitianParts
open AnisotropicColumnSums
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.SkewHermitianParts
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) : InLieW k r z 0 :=
  ⟨⟨by simp, fun a _ => by simp⟩, by simp⟩
end Formalism.FourierDecayAlt.P.SkewHermitianParts
