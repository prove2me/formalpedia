-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.mon1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:08:23.39707+00:00
-- url     : https://prove2.me/submissions/583634d3-db89-4419-8558-51ac2f0b04f1

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
theorem _root_.solution {z zi w wi gi : M} (hz : z * zi = 1) (hw : w * wi = 1) (c1 : Commute gi zi)
    (c2 : Commute w zi) (c3 : Commute gi wi) : z * w * gi * zi * wi = gi := by
  calc z * w * gi * zi * wi = z * (w * (gi * zi)) * wi := by simp only [mul_assoc]
    _ = z * (w * zi * gi) * wi := by rw [c1.eq, ← mul_assoc w zi gi]
    _ = z * zi * (w * (gi * wi)) := by rw [c2.eq]; simp only [mul_assoc]
    _ = gi := by rw [hz, one_mul, c3.eq, ← mul_assoc w wi gi, hw, one_mul]
end Formalism.FourierDecayAlt.P.Fr8
