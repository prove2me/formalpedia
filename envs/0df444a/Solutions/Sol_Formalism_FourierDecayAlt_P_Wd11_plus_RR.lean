-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd11.plus_RR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:20:17.061892+00:00
-- url     : https://prove2.me/submissions/baea6ca6-6172-4c76-b832-f4f5719b1101

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteTransposedRMatrix
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_lift
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_insL_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_comm_insL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_conjTranspose
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_ins_sandwich
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_cen_Uinv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd11_Uinv_conj_mul
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
theorem _root_.solution (a : S) (s : K) {V Vi RR : SlopeTestRemainingChoices S A} {T : M2 (SlopeTestRemainingChoices S A)}
    (hV : FreeOf a V) (hVi : FreeOf a Vi) (hRR : FreeOf a RR) (hT : FreeOf2 a T)
    (h1 : V * Vi = 1) (h3 : star V * RR * V = RR)
    (h4 : d0 Vi * T * d0 V = lift0 (Um (A := A) s)ᴴ * T * lift0 (Um (A := A) s)) :
    star (ins a (lift0 (Uinv (A := A) s)) * V) * (RR * ins a T) *
        (ins a (lift0 (Uinv (A := A) s)) * V) = RR * ins a T := by
  have hs : star (ins a (lift0 (Uinv (A := A) s)) : SlopeTestRemainingChoices S A) = ins a (lift0 (Uinv (A := A) s)ᴴ) :=
    insL_star a _
  refine rr_step (Vi := Vi) (L := ins a (lift0 (Um (A := A) s)ᴴ)) (R := ins a (lift0 (Um (A := A) s)))
    h1 h3 (comm_insL (cen_Uinv s) hV).symm ?_ ?_ ?_ ?_ (insL_Um_Uinv a s)
  · rw [hs]; exact (comm_insL (cen_conjTranspose (cen_Uinv s)) hRR).symm
  · rw [hs]; exact (comm_insL (cen_conjTranspose (cen_Uinv s)) hV).symm
  · rw [← ins_sandwich hVi, h4, ins_mul a _ _ (freeOf2_mul (freeOf2_lift a _) hT),
      ins_mul a _ _ (freeOf2_lift a _)]
  · rw [hs, ← insL_mul, Uinv_conj_mul, insL_one]
end Formalism.FourierDecayAlt.P.Wd11
