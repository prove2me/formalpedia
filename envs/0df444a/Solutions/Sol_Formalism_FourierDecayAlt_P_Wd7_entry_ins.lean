-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.entry_ins
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:09:53.894422+00:00
-- url     : https://prove2.me/submissions/962aa173-a23c-4ce1-804a-3cf05660ce03

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_eU_mul_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_free_apply_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd6_eU_mul_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd7
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A] [StarModule K A]
  [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution (a : S) (R : SlopeTestRemainingChoices S A) (M : M2 (SlopeTestRemainingChoices S A)) (hR : FreeOf a R) (hM : FreeOf2 a M) :
    (R * ins a M) e1 e1 = (R * M 0 0) e1 e1 := by
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases hz : z a = 0
  · congr 1
    unfold ins
    simp only [Fin.sum_univ_two, Matrix.add_apply, eU_mul_apply, hz, if_true]
    have hu : Function.update z a 0 = z := by rw [← hz]; exact Function.update_eq_self a z
    have h1 : ∀ i, (M i 1) (Function.update z a 1) e1 = 0 := fun i => by
      apply free_apply_zero (hM i 1)
      simp [e1]
    simp [hu, h1]
  · have h0 : R e1 z = 0 := free_apply_zero hR (fun h => hz h.symm)
    rw [h0, zero_mul, zero_mul]
end Formalism.FourierDecayAlt.P.Wd7
