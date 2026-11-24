-- Prove2me | solution 1 for Formalism.YangianSpanCharacter.P.isLaxFamilyConstantModel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:42:02.736277+00:00
-- url     : https://prove2.me/submissions/6cca7f86-e52d-4d8b-b7ce-df7a746b83d8

import Definitions.Def_Formalism_YangianSpanCharacter_StatementY
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRTTProofs_SymplecticTransposeEntryZeroOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.YangianSpanCharacter Formalism.YangianSpanCharacter.P
open Matrix Formalism.YangianSpanCharacter.Y
namespace Formalism.YangianSpanCharacter.P
theorem _root_.solution : Formalism.YangianSpanCharacter.Y.ModHypModel := by
  unfold Formalism.YangianSpanCharacter.Y.ModHypModel Formalism.YangianSpanCharacter.Y.ModHyp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v i j k l
    dsimp only
    rw [smul_eq_mul]
    ring
  · intro Y
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]
  · intro Y
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Formalism.YangianSpanCharacter.T.J, Matrix.mul_apply, Fin.sum_univ_two]
  · intro u _
    norm_num
  · intro u v
    exact Commute.all _ _
  · intro u v
    exact Commute.all _ _
end Formalism.YangianSpanCharacter.P
