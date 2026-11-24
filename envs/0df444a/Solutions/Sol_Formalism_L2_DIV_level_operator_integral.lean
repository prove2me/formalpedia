-- Prove2me | solution 1 for Formalism.L2.DIV.level_operator_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:26.958966+00:00
-- url     : https://prove2.me/submissions/2867636d-ae63-4b02-ad98-41ecab84fd17

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_action_preserves_lattice
import Theorems.Thm_Formalism_L2_DIV_good_at_spec
import Theorems.Thm_Formalism_L2_DIV_boundsIHyps_of
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
theorem _root_.solution : BoundsIHyps := by
  exact boundsIHyps_of orthogonal_projection_spec good_at_spec action_preserves_lattice
end Formalism.L2.DIV
