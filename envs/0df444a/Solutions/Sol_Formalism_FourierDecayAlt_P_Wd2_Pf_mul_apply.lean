-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.Pf_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:09:50.604445+00:00
-- url     : https://prove2.me/submissions/6eb5e8e3-a752-42ff-bb2d-4411421fb382

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
theorem _root_.solution (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (i k : Fin 2) (p : Fin 2 × Fin 2) :
    (Pf B * X) (i, k) p = X (k, i) p := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  fin_cases i <;> fin_cases k <;> simp [Pf]
end Formalism.FourierDecayAlt.P.Wd2
