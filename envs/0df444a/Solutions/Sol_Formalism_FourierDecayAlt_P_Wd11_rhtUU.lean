-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.rhtUU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T14:05:03.375491+00:00
-- url     : https://prove2.me/submissions/bc058ad3-2840-4982-a917-5740de9d3e42

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_commute_liftMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_Um
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_exchange_conj_through_partial_flip

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
theorem _root_.solution (b : S) (d s : K) :
    d0 (ins b (lift0 (Um (A := A) (star s)))) * Rht0 b d * lift0 (Um (A := A) s)ᴴ =
      lift0 (Um (A := A) s)ᴴ * Rht0 b d * d0 (ins b (lift0 (Um (A := A) (star s)))) := by
  have hc := (diagScalar_commute_liftMatrix (S := S) (cen_conjTranspose (cen_Um (A := A) s))
    (ins b (lift0 (Um (A := A) (star s))))).eq
  unfold Rht0
  simp only [mul_smul_comm, smul_mul_assoc, mul_sub, sub_mul, exchange_conj_through_partial_flip, mul_one, hc]
end Formalism.FourierDecayAlt.P.Wd11
