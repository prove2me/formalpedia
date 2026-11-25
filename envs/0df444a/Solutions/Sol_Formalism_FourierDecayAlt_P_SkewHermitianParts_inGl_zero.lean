-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.SkewHermitianParts.inGl_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:54:13.87672+00:00
-- url     : https://prove2.me/submissions/571539c4-4345-4145-897b-b6fc2a22dd48

import Definitions.Def_Formalism_HermitianCurvature_FrameExists2
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ExistsFrameTwo
import Theorems.Thm_Formalism_FourierDecayAlt_P_SkewHermitianParts_inLie_zero

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
theorem _root_.solution (z : Fin (2 * r + k + 1) → ℂ) : InGlW k r z 0 := by
  have h1 : hpart1 (Hpk k r) (0 : Mx k r) = 0 := by simp [hpart1]
  have h2 : hpart2 (Hpk k r) (0 : Mx k r) = 0 := by simp [hpart2]
  unfold InGlW
  rw [h1, h2]
  exact ⟨inLie_zero z, inLie_zero z⟩
end Formalism.FourierDecayAlt.P.SkewHermitianParts
