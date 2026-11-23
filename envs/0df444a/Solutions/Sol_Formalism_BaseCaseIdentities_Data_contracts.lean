-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.contracts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:18.371018+00:00
-- url     : https://prove2.me/submissions/15f897dd-c123-4c86-b57a-b68457fd51ee

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow_sub_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_Psi
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_one_lt_l

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open Formalism Formalism.BaseCaseIdentities
noncomputable section
open Classical
variable {k : Type*} [Field k] {Z : Type*} {C : Type*}
open Formalism.BaseCaseIdentities.Data
variable [Fintype Z] [Fintype C] (D : Data k Z C)
namespace Formalism.BaseCaseIdentities.Data
theorem _root_.solution : D.Contraction := by
  intro t t' n ht ht' h b A hA
  rw [map_sub, coeff_Psi, coeff_Psi, sub_eq_zero]
  congr 1
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_Icc] at hj
  have hl : D.l ≤ D.l ^ j := Nat.le_self_pow (by omega) _
  have hN : 1 ≤ D.l ^ j := Nat.one_le_pow _ _ (by have := D.one_lt_l; omega)
  have hc := OrdGE.pow_sub_pow (ht c) (ht' c) (h c) hN A (by omega)
  rw [map_sub, sub_eq_zero] at hc
  rw [hc]
end Formalism.BaseCaseIdentities.Data
