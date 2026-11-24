-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.mon2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:08:24.371579+00:00
-- url     : https://prove2.me/submissions/1a537bac-dd88-4c8e-98c7-e6b447ed2b8f

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
theorem _root_.solution {z zi w wi g gi : M} (hz : z * zi = 1) (hw : w * wi = 1) (hg : gi * g = 1) :
    z * w * gi * (g * wi) * (zi * g) = g := by
  simp only [mul_assoc]
  rw [← mul_assoc gi g, hg, one_mul, ← mul_assoc w wi, hw, one_mul, ← mul_assoc z zi, hz, one_mul]
end Formalism.FourierDecayAlt.P.Fr8
