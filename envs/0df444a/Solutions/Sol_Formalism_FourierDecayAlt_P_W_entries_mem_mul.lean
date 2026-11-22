-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.W.entries_mem_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:37:50.046008+00:00
-- url     : https://prove2.me/submissions/cf017075-2eb3-4a88-b977-ad69e3af8844

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
theorem _root_.solution (M N : Matrix (Fin 2) (Fin 2) B) : E2 (M * N) = E2 M * E2 N := by
  unfold Formalism.YangianSpanCharacter.T.E2
  ext ⟨i, k⟩ ⟨j, l⟩
  fin_cases i <;> fin_cases k <;> fin_cases j <;> fin_cases l <;>
    simp [Matrix.mul_apply, Matrix.one_apply, Fintype.sum_prod_type, Fin.sum_univ_two]
end Formalism.FourierDecayAlt.P.W
