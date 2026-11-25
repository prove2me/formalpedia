-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieQL.cK_coordK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:34:09.373741+00:00
-- url     : https://prove2.me/submissions/291c0087-b12a-4411-92bc-c454562aa90b

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
theorem _root_.solution (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) (q : Q) (i : Fin ρ) :
    cK b c (coordK b q) i = algebraMap O (FractionRing O) (c i q) := by
  rw [c_eq_sum b c i q, map_sum]
  simp only [cK, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, coordK,
    LinearMap.coe_mk, AddHom.coe_mk, map_mul]
end Formalism.L2.Pj.QAt.TieQL
