-- Prove2me | solution 1 for Formalism.L2.DIV.mem_kills
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:25:11.958521+00:00
-- url     : https://prove2.me/submissions/458b265c-d00c-45b8-85f1-26d99c1a65e7

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_QuotientMetricDivisors_RatHermLcvTwist
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism Formalism.L2 Formalism.L2.DIV
namespace Formalism.L2.DIV
theorem _root_.solution {G A : Type} [Group G] [CommGroup A] {H : Subgroup G} {ξ : G →* A} :
    ξ ∈ kills A H ↔ H ≤ ξ.ker := Iff.rfl
end Formalism.L2.DIV
