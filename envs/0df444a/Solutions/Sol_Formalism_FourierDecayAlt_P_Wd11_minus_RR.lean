-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.minus_RR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T14:20:59.440815+00:00
-- url     : https://prove2.me/submissions/d1a98524-e16c-46e4-aa33-f0272c3db3d9

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_comm_insL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_ins_sandwich
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_diagScalar_sandwich_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_liftMatrix_mul_transpose_of_central
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_mul_lift0_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_Um
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_Uinv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_Um_conjTranspose_transpose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_Uinv_star_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_rr_step
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_Um_Uinv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_mul


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
theorem _root_.solution (b : S) (s : K) {V Vi RR : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)}
    (hV : FreeOf b V) (hVi : FreeOf b Vi) (hRR : FreeOf b RR) (hT : FreeOf2 b T)
    (h1 : V * Vi = 1) (h3 : star V * RR * V = RR)
    (h4 : d0 Vi * T * d0 V = lift0 (Um (A := A) s)ᴴ * T * lift0 (Um (A := A) s)) :
    star (ins b (lift0 (Uinv (A := A) (star s))) * V) * (RR * ins b Tᵀ) *
        (ins b (lift0 (Uinv (A := A) (star s))) * V) = RR * ins b Tᵀ := by
  have hs : star (ins b (lift0 (Uinv (A := A) (star s))) : SlopeTestRemainingChoices S A) =
      ins b (lift0 (Uinv (A := A) (star s))ᴴ) := insL_star b _
  refine rr_step (Vi := Vi) (L := ins b (lift0 (Um (A := A) s)ᵀ))
    (R := ins b (lift0 (Um (A := A) (star s))))
    h1 h3 (comm_insL (cen_Uinv _) hV).symm ?_ ?_ ?_ ?_ (insL_Um_Uinv b _)
  · rw [hs]; exact (comm_insL (cen_conjTranspose (cen_Uinv _)) hRR).symm
  · rw [hs]; exact (comm_insL (cen_conjTranspose (cen_Uinv _)) hV).symm
  · rw [← ins_sandwich hVi, ← diagScalar_sandwich_transpose, h4, mul_lift0_transpose (cen_Um s),
      liftMatrix_mul_transpose_of_central (cen_conjTranspose (cen_Um s)), Um_conjTranspose_transpose, ← mul_assoc,
      ins_mul b _ _ (freeOf2_mul (freeOf2_lift b _) (freeOf2_transpose hT)),
      ins_mul b _ _ (freeOf2_lift b _)]
  · rw [hs, ← insL_mul, Uinv_star_mul, insL_one]
end Formalism.FourierDecayAlt.P.Wd11
