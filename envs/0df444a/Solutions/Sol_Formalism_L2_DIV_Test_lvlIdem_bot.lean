-- Prove2me | solution 1 for Formalism.L2.DIV.Test.lvlIdem_bot
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:48.208551+00:00
-- url     : https://prove2.me/submissions/d6a69787-3e79-495a-8a73-fe930a1c3709

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_level_idempotent_bot

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
open Formalism Formalism.L2 Formalism.L2.DIV Formalism.L2.DIV.Test
open Formalism.DivisionValues
variable (K : Type) [Field K] [NumberField K] [StarRing K] (G : Type) [Group G] [Fintype G]
namespace Formalism.L2.DIV.Test
theorem _root_.solution (ψ : (⊥ : Subgroup G) →* Kˣ) : lvlIdem (⊥ : Subgroup G) ψ = 1 := by
  exact level_idempotent_bot K G ψ
end Formalism.L2.DIV.Test
