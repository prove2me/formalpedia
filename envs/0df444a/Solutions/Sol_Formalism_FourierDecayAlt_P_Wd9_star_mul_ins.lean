-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd9.star_mul_ins
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:08:38.302324+00:00
-- url     : https://prove2.me/submissions/ac30a999-d6d1-4970-a567-6c6a82419b6c

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PositionInsertionDiagonalCompat
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondEmbedMulFirstEmbedApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiagScalarCommuteOfEntries
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf2_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_freeOf_diagScalar
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd9_mul_ins
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd1_ins_star
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd3_mul_ins


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
theorem _root_.solution {a : S} {RR : SlopeTestRemainingChoices S A} (hR : FreeOf a RR) {M : M2 (SlopeTestRemainingChoices S A)} (hM : FreeOf2 a M)
    (h : (d0 RR * M)ᴴ = d0 RR * M) : star (RR * ins a M) = RR * ins a M := by
  rw [mul_ins hR, Wd1.ins_star a _ (freeOf2_mul (freeOf_diagScalar hR) hM), h]
end Formalism.FourierDecayAlt.P.Wd9
