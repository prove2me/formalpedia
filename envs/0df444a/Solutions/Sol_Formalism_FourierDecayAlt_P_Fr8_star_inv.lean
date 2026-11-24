-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.star_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:08:30.646814+00:00
-- url     : https://prove2.me/submissions/96e3b91d-21e9-4cb7-80d8-5a0b0d29fc07

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
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution {R : Type} [Ring R] [StarRing R] {a b a' b' : R} (h1 : a * b = 1) (h : star a = a')
    (h2 : a' * b' = 1) : star b = b' := by
  have e : star b * a' = 1 := by rw [← h, ← star_mul, h1, star_one]
  calc star b = star b * (a' * b') := by rw [h2, mul_one]
    _ = b' := by rw [← mul_assoc, e, one_mul]
end Formalism.FourierDecayAlt.P.Fr8
