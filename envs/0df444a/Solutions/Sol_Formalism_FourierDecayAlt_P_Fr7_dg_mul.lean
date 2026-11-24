-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.dg_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:10.831046+00:00
-- url     : https://prove2.me/submissions/e4b36e1d-e880-4e77-b352-3f801ab7245d

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul


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
theorem _root_.solution {p q p' q' : SlopeTestRemainingChoices S A} (hp : FreeOf a p) (hq : FreeOf a q) :
    ins a !![p, 0; 0, q] * ins a !![p', 0; 0, q'] = ins a !![p * p', 0; 0, q * q'] := by
  rw [← ins_mul a _ _ (free2 hp free_zero free_zero hq)]
  congr 1
  rw [Matrix.mul_fin_two]
  simp
end Formalism.FourierDecayAlt.P.Fr7
