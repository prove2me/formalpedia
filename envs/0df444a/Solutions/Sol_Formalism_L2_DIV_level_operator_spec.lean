-- Prove2me | solution 1 for Formalism.L2.DIV.level_operator_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:16:50.625435+00:00
-- url     : https://prove2.me/submissions/c8651f39-2ed9-47fa-bb12-50dd9fcb5ac2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_level_idempotent_spec
import Theorems.Thm_Formalism_L2_DIV_lvlOpSpec_of
import Theorems.Thm_Formalism_L2_DIV_orthogonal_projection_spec

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
theorem _root_.solution : LvlOpSpec := by
  exact lvlOpSpec_of orthogonal_projection_spec level_idempotent_spec
end Formalism.L2.DIV
