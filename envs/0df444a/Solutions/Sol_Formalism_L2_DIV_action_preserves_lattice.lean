-- Prove2me | solution 1 for Formalism.L2.DIV.action_preserves_lattice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:23.190803+00:00
-- url     : https://prove2.me/submissions/3762f2ab-d660-4f5b-85c8-3443b20161e5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_GoodPartHermitianSpec
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ClassSumLemmas
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ClassSumDualGeOfFamily
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_ProjLemmas
import Theorems.Thm_Formalism_L2_DIV_CSD_I_actMat
import Theorems.Thm_Formalism_L2_DIV_mem_valLatF
import Theorems.Thm_Formalism_DivisionValues_ValuationLatticeField_mem_valLatF


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
theorem _root_.solution : ActLat := by
  intro K _ _ _ S G _ _ r hr t
  constructor
  · intro x hx
    unfold CSD.nabLat at hx ⊢
    rw [mem_valLatF] at hx ⊢
    intro c
    rw [S.I_actMat r t x]
    exact hr.nab_stable t (S.basis.equivFun.symm x) hx c
  · intro x hx
    unfold CSD.delLat at hx ⊢
    rw [mem_valLatF] at hx ⊢
    intro c
    rw [S.I_actMat r t x]
    exact hr.del_stable t (S.basis.equivFun.symm x) hx c
end Formalism.L2.DIV
