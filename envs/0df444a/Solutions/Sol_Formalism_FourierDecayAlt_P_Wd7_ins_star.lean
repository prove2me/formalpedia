-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd7.ins_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:01:38.240525+00:00
-- url     : https://prove2.me/submissions/a20f6e79-3149-4f57-a680-14c69d5b8469

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_EntryCommuteTransposedRMatrix
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ScalarCommuteTransposedRMatrixEntry
import Theorems.Thm_Formalism_FourierDecayAlt_P_Wd7_star_eU

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
variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]
namespace Formalism.FourierDecayAlt.P.Wd7
theorem _root_.solution [StarRing A] (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 a M) :
    star (ins a M) = ins a Mᴴ := by
  unfold ins
  have key : ∀ i j : Fin 2, star ((eU a i j : SlopeTestRemainingChoices S A) * M i j) = eU a j i * Mᴴ j i := by
    intro i j
    rw [star_mul, star_eU, Matrix.conjTranspose_apply]
    have h := (hM i j i j).star_star
    rw [star_eU] at h
    exact h.eq.symm
  simp only [star_sum, key]
  exact Finset.sum_comm
end Formalism.FourierDecayAlt.P.Wd7
