-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Fr7.dg_star
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:59:26.512955+00:00
-- url     : https://prove2.me/submissions/edd0f90e-0444-463c-9de9-9320fb62b6e8

import Definitions.Def_Formalism_HermitianCurvature_StatementFr
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PlusLetterFrameOfData
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Fr7_free2
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_star


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
theorem _root_.solution {p q : SlopeTestRemainingChoices S A} (hp : FreeOf a p) (hq : FreeOf a q) :
    star (ins a !![p, 0; 0, q]) = ins a !![star p, 0; 0, star q] := by
  rw [ins_star a _ (free2 hp free_zero free_zero hq)]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
end Formalism.FourierDecayAlt.P.Fr7
