-- Prove2me | solution 1 for Formalism.L2.DIV.good_at_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:51:06.661985+00:00
-- url     : https://prove2.me/submissions/0cce3f95-52e1-4726-966c-9e165b8de832

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_level_idempotent_spec
import Theorems.Thm_Formalism_L2_DIV_goodAtSpec_of
import Theorems.Thm_Formalism_L2_DIV_idempotent_spec

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
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.DivisionValues
namespace Formalism.L2.DIV
theorem _root_.solution : GoodAtSpec := by
  exact goodAtSpec_of idempotent_spec level_idempotent_spec
end Formalism.L2.DIV
