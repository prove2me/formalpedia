-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CapelliTwoByTwo.bc_herm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:18:59.246729+00:00
-- url     : https://prove2.me/submissions/9decc493-1508-466d-b5d7-9473cec2580f

import Definitions.Def_Formalism_HermitianCurvature_FrameMinor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OperatorRepresentations
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LemmaDDeterminantIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliCoordinates
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AnisotropicColumnSums
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CapelliTwoByTwo

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
open Formalism.FourierDecayAlt.P.CapelliTwoByTwo
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.CapelliTwoByTwo
theorem _root_.solution {y x : Fin (2 * r + k + 1) → ℂ} {Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [y, x] Bs) (j : Fin (mdim k r (Fin.last r))) (w : Fin (2 * r + k + 1) → ℂ) (hw : w ∈ [y, x]) :
    herm (Hpk k r) (bc k r y x Bs j) w =
      if j.val = 0 then herm (Hpk k r) y w else if j.val = 1 then herm (Hpk k r) x w else 0 := by
  have hBw : ∀ a, herm (Hpk k r) (Bs a) w = 0 := fun a => hB.2.2 a w hw
  by_cases h0 : j.val = 0
  · rw [bc, dif_pos h0, if_pos h0]
  · by_cases h1 : j.val = 1
    · rw [bc, dif_neg h0, dif_pos h1, if_neg h0, if_pos h1]
    · rw [bc, dif_neg h0, dif_neg h1, if_neg h0, if_neg h1, hBw]
end Formalism.FourierDecayAlt.P.CapelliTwoByTwo
