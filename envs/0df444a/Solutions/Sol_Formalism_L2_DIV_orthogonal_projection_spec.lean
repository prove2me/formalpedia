-- Prove2me | solution 1 for Formalism.L2.DIV.orthogonal_projection_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T09:23:31.793658+00:00
-- url     : https://prove2.me/submissions/a85a58d4-63d5-4e18-a742-68ea29e25f0a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_image_idempotent_spec
import Theorems.Thm_Formalism_L2_DIV_group_action_matrix_hom
import Theorems.Thm_Formalism_L2_DIV_group_action_matrix_adjoint
import Theorems.Thm_Formalism_L2_DIV_cutOrthProj_of

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
theorem _root_.solution : CutOrthProj := by
  exact cutOrthProj_of image_idempotent_spec group_action_matrix_hom group_action_matrix_adjoint
end Formalism.L2.DIV
