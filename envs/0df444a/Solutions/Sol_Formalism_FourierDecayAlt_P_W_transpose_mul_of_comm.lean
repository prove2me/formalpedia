-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.W.transpose_mul_of_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:32:56.859804+00:00
-- url     : https://prove2.me/submissions/add6361c-1b10-43e0-82b2-1d8e62ed1b91

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
theorem _root_.solution (A C : Matrix (Fin 2) (Fin 2) B)
    (h : ∀ i j k l, A i j * C k l = C k l * A i j) : (A * C)ᵀ = Cᵀ * Aᵀ := by
  ext i j
  simp [Matrix.mul_apply, Fin.sum_univ_two, h]
end Formalism.FourierDecayAlt.P.W
