-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.comm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:08:28.23615+00:00
-- url     : https://prove2.me/submissions/c7e0be44-d02f-483c-acfb-793876fd8a22

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
theorem _root_.solution {x xi g : M} (h1 : x * xi = 1) (h2 : xi * x = 1) (c : Commute x g) : Commute xi g := by
  show xi * g = g * xi
  calc xi * g = xi * g * (x * xi) := by rw [h1, mul_one]
    _ = xi * (g * x) * xi := by simp only [mul_assoc]
    _ = xi * (x * g) * xi := by rw [← c.eq]
    _ = g * xi := by rw [← mul_assoc xi x g, h2, one_mul]
end Formalism.FourierDecayAlt.P.Fr8
