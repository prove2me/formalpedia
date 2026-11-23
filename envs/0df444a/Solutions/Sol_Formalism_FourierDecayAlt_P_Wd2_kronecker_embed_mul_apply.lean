-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.kronecker_embed_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:06.935602+00:00
-- url     : https://prove2.me/submissions/4d6e060d-aa81-4c91-9f28-aaedf1ce66b5

import Definitions.Def_Formalism_HermitianCurvature_StatementWd
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KroneckerEmbedMulApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Wd2
open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd
variable {K B : Type} [CommRing K] [Ring B] [Algebra K B]
namespace Formalism.FourierDecayAlt.P.Wd2
theorem _root_.solution (M N : Matrix (Fin 2) (Fin 2) B) (i k j l : Fin 2) :
    (E2 N * E1 M) (i, k) (j, l) = N k l * M i j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2]
end Formalism.FourierDecayAlt.P.Wd2
