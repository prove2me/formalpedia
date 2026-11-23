-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.comm_dg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:42:04.416967+00:00
-- url     : https://prove2.me/submissions/b63b481a-95db-49b3-b0ce-8d66fef563f7

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_comm2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_comm


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
theorem _root_.solution {b p q : SlopeTestRemainingChoices S A} (hb : FreeOf a b) (h1 : Commute b p) (h2 : Commute b q) :
    Commute b (ins a !![p, 0; 0, q]) :=
  ins_comm a _ b hb (comm2 h1 (Commute.zero_right b) (Commute.zero_right b) h2)
end Formalism.FourierDecayAlt.P.Fr7
