-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Wd2.mul_Pf_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:10:07.323026+00:00
-- url     : https://prove2.me/submissions/253d5f32-3cae-47e4-91fd-071973fc5361

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
theorem _root_.solution (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (p : Fin 2 × Fin 2) (j l : Fin 2) :
    (X * Pf B) p (j, l) = X p (l, j) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  fin_cases j <;> fin_cases l <;> simp [Pf]
end Formalism.FourierDecayAlt.P.Wd2
