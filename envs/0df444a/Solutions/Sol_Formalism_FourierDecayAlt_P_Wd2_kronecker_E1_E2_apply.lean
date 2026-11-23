-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.kronecker_E1_E2_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:51.120799+00:00
-- url     : https://prove2.me/submissions/c143e0d4-977a-4b85-aefa-ce84fd4df0df

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
    (E1 M * E2 N) (i, k) (j, l) = M i j * N k l := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2]
end Formalism.FourierDecayAlt.P.Wd2
