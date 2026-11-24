-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.psiM_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:02:12.133788+00:00
-- url     : https://prove2.me/submissions/d62f7c9f-7c05-4ca3-9977-f988c106b1c0

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_ins_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_J_matrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul
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
theorem _root_.solution (TT : K → M2 (SlopeTestRemainingChoices S A)) (q : K → K) (a : S) (Yb : K) :
    PsiM TT q a Yb = (q (Yb - 1))⁻¹ • (ins a JJ * ins a (TT (Yb - 1))) := by
  rw [PsiM, ins_smul, Wd1.ins_mul a _ _ (freeOf_J_matrix a)]
end Formalism.FourierDecayAlt.P.Wd9
