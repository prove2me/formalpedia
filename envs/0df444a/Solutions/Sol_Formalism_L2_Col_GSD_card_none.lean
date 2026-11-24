-- Prove2me | solution 1 for Formalism.L2.Col.GSD.card_none
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:13:49.272853+00:00
-- url     : https://prove2.me/submissions/580e5571-629e-4a02-8387-33b51e6d32d9

import Definitions.Def_Formalism_LocalToGlobal_Columns_RhoEqOfSmulEq
import Definitions.Def_Formalism_ThetaLiftIndependence_Statement
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DoubleCosetDecompositionAll
import Definitions.Def_Formalism_LocalToGlobal_Columns_GSetLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
open Formalism.DivisionValues Formalism.L2.DIV
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open Formalism.L2.Col.GSD
variable (K)
namespace Formalism.L2.Col.GSD
theorem _root_.solution : Nat.card (MulAction.stabilizer ℤˣ (none : Option ℤˣ)) = 2 := by
  rw [show MulAction.stabilizer ℤˣ (none : Option ℤˣ) = ⊤ from (Subgroup.eq_top_iff' _).mpr fun g => rfl,
    Subgroup.card_top, Nat.card_eq_fintype_card]
  first | rfl | decide | simp
end Formalism.L2.Col.GSD
