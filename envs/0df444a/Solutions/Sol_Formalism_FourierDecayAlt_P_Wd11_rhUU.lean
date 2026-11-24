-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.rhUU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T13:49:22.530671+00:00
-- url     : https://prove2.me/submissions/7edb26fe-a1e0-4f92-b8d2-47b07e89a916

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_UU_commute_flip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd11
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P.Wd1
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd11
theorem _root_.solution (a : S) (D s : K) :
    lift0 (Um (A := A) s) * d0 (ins a (lift0 (Um (A := A) s))) * Rh0 a D =
      Rh0 a D * (lift0 (Um (A := A) s) * d0 (ins a (lift0 (Um (A := A) s)))) := by
  unfold Rh0
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, UU_commute_flip, mul_smul_comm, smul_mul_assoc,
    mul_one, one_mul]
end Formalism.FourierDecayAlt.P.Wd11
