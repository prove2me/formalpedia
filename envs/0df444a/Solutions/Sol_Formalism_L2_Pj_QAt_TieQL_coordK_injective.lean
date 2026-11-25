-- Prove2me | solution 1 for Formalism.L2.Pj.QAt.TieQL.coordK_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:42:49.859408+00:00
-- url     : https://prove2.me/submissions/7ea56311-1509-4c0f-96e6-e33cb5ce2634

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
theorem _root_.solution (b : Basis (Fin ρ) O Q) : Function.Injective (coordK b) := by
  intro x y h
  apply b.repr.injective
  ext k
  have hk := congrFun h k
  simp only [coordK, LinearMap.coe_mk, AddHom.coe_mk] at hk
  exact IsFractionRing.injective O (FractionRing O) hk
end Formalism.L2.Pj.QAt.TieQL
