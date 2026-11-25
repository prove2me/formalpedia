-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieQL.c_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:25:18.084515+00:00
-- url     : https://prove2.me/submissions/544dc7de-26c5-40a6-ad3f-222bf646fa25

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_Rationality_QuotSt
import Definitions.Def_Formalism_FilteredPoleLength_LocalDescentLevels_MemSpanBasisFun
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ArchimedeanQuadraticData_QuotLocalOfQuotientLength

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
theorem _root_.solution (b : Basis (Fin ρ) O Q) (c : Fin ρ → (Q →ₗ[O] O)) (i : Fin ρ) (q : Q) :
    c i q = ∑ k, matA b c i k * b.repr q k := by
  conv_lhs => rw [← b.sum_repr q]
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl
end Formalism.L2.Pj.QAt.TieQL
