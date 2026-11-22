-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.W.first_embedding_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:50.035247+00:00
-- url     : https://prove2.me/submissions/9defaed1-a1b4-4534-a66a-db39473c5bf3

import Definitions.Def_Formalism_HermitianCurvature_StatementW
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.W
open Matrix Formalism.YangianSpanCharacter.T NumberField Formalism.FourierDecayAlt.W
variable {R B : Type} [CommRing R] [Ring B] [Algebra R B]
namespace Formalism.FourierDecayAlt.P.W
theorem _root_.solution (M N : Matrix (Fin 2) (Fin 2) B) : E1 (M * N) = E1 M * E1 N := by
  unfold Formalism.YangianSpanCharacter.T.E1
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
end Formalism.FourierDecayAlt.P.W
