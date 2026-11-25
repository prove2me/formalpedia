-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieQL.det_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:42:51.374991+00:00
-- url     : https://prove2.me/submissions/757fbf04-63fc-4b7f-a93c-007213967c0b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_QuotLocalOfQuotientLength
import Theorems.Thm_Formalism_L2_Pj_QAt_TieQL_c_eq_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.QAt
open Formalism.L2.Pj.QAt.TieQL
open Module
variable {O Q : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [AddCommGroup Q] [Module O Q] {ρ : ℕ}
namespace Formalism.L2.Pj.QAt.TieQL
theorem _root_.solution (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) (th : Fin ρ → Q) :
    (Matrix.of fun i j => c i (th j)) = matA b c * Matrix.of fun k j => b.repr (th j) k := by
  ext i j
  rw [Matrix.of_apply, Matrix.mul_apply, c_eq_sum b c i (th j)]
  rfl
end Formalism.L2.Pj.QAt.TieQL
