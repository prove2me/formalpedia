-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.mon3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:08:25.668645+00:00
-- url     : https://prove2.me/submissions/0c8e2d57-11d0-475d-9b45-92d04cc053ea

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuasiDeterminantFromEntries
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussFormMinusLetter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr8
variable {M : Type} [Monoid M]
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution {z zi w wi g gi : M} (hz : zi * z = 1) (hw : wi * w = 1) (hg : g * gi = 1)
    (c : Commute wi z) : g * zi * wi * (z * w * gi) = 1 := by
  simp only [mul_assoc]
  rw [← mul_assoc wi z, c.eq, mul_assoc z wi, ← mul_assoc zi z, hz, one_mul, ← mul_assoc wi w, hw, one_mul, hg]
end Formalism.FourierDecayAlt.P.Fr8
