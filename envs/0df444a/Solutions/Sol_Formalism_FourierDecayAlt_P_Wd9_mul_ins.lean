-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.mul_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:12.143414+00:00
-- url     : https://prove2.me/submissions/cc231c7e-d484-42ae-9d9f-4dc5994cc79a

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_diagScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_insert_diagonal_extract
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_ins_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd9
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
local notation "JJ" => (Formalism.YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A))
namespace Formalism.FourierDecayAlt.P.Wd9
theorem _root_.solution {a : S} {RR : SlopeTestRemainingChoices S A} (hR : FreeOf a RR) (M : M2 (SlopeTestRemainingChoices S A)) :
    RR * ins a M = ins a (d0 RR * M) := by
  rw [Wd1.ins_mul a _ _ (freeOf_diagScalar hR), Wd1.insert_diagonal_extract]
end Formalism.FourierDecayAlt.P.Wd9
