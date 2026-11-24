-- Prove2me | solution 1 for Formalism.L2.DIV.fockSQ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:52:48.762018+00:00
-- url     : https://prove2.me/submissions/686fd18e-9bf8-4932-9461-fc1fc90baddd

import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefModLemmas
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.L2 Formalism.L2.DIV
open Formalism.BasicNotions
namespace Formalism.L2.DIV
theorem _root_.solution : FockSQ := by
  intro K _ _ _ σ f g
  have hinj : Function.Injective (algebraMap ℚ K) := (algebraMap ℚ K).injective
  unfold fockS Formalism.GradedWeylDivisibility.fockQ mfact
  rw [support_map_of_injective _ hinj, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [coeff_map, map_mul, map_natCast, eq_ratCast, star_ratCast]
end Formalism.L2.DIV
