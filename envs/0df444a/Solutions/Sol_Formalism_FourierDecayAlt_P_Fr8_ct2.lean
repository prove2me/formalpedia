-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.ct2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:06:37.783785+00:00
-- url     : https://prove2.me/submissions/7c338e1b-5305-4a14-a39d-7cd3e00723e7

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
theorem _root_.solution {R : Type} [Star R] (a b c d : R) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) R)ᴴ = !![star a, star c; star b, star d] := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
end Formalism.FourierDecayAlt.P.Fr8
