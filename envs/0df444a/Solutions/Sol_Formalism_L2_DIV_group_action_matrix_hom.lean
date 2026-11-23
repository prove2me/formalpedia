-- Prove2me | solution 1 for Formalism.L2.DIV.group_action_matrix_hom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:36.940438+00:00
-- url     : https://prove2.me/submissions/a6d68273-89e9-4db6-990a-679cbe0d3e22

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_gaMat_eq_lift

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
theorem _root_.solution : GaMatHom := by
  intro K _ _ _ S G _ _ r
  exact ⟨by rw [S.gaMat_eq_lift r, map_one], fun a b => by simp only [S.gaMat_eq_lift r, map_mul]⟩
end Formalism.L2.DIV
