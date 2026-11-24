-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr8.free2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:06:49.536143+00:00
-- url     : https://prove2.me/submissions/58ca87c8-4dfb-4741-aa39-1998d10a10b4

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
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Fr8
theorem _root_.solution {c : S} {p q r s : SlopeTestRemainingChoices S A} (hp : FreeOf c p) (hq : FreeOf c q) (hr : FreeOf c r)
    (hs : FreeOf c s) : FreeOf2 c !![p, q; r, s] := by
  unfold Formalism.FourierDecayAlt.Wd.FreeOf2
  intro i j
  fin_cases i <;> fin_cases j <;> simp [hp, hq, hr, hs]
end Formalism.FourierDecayAlt.P.Fr8
