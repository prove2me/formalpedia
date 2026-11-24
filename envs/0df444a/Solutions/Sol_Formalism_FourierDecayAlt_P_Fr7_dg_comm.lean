-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.dg_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:20.971308+00:00
-- url     : https://prove2.me/submissions/61e4b362-2a3a-430f-9acb-425e44dba981

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_dg_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.YangianSpanCharacter.T Formalism.YangianSpanCharacter.Y Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Fr7
open Formalism.FourierDecayAlt.P.Wd1
variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [Fintype S] [DecidableEq S] {a : S}
namespace Formalism.FourierDecayAlt.P.Fr7
theorem _root_.solution {p q p' q' : SlopeTestRemainingChoices S A} (hp : FreeOf a p) (hq : FreeOf a q) (hp' : FreeOf a p')
    (hq' : FreeOf a q') (h1 : Commute p p') (h2 : Commute q q') :
    Commute (ins a !![p, 0; 0, q]) (ins a !![p', 0; 0, q']) := by
  show _ * _ = _ * _
  rw [dg_mul hp hq, dg_mul hp' hq', h1.eq, h2.eq]
end Formalism.FourierDecayAlt.P.Fr7
