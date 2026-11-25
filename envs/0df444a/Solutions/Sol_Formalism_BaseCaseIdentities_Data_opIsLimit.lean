-- Prove2me | solution 1 for Formalism.BaseCaseIdentities.Data.opIsLimit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:34:21.515437+00:00
-- url     : https://prove2.me/submissions/acbb4961-1164-44bb-b787-7cfc88200cba

import Definitions.Def_Formalism_FrobeniusBaseCase_Statement
import Definitions.Def_Formalism_FrobeniusBaseCase_FrobeniusBaseCaseProofs_HasUniqueFixedPoint
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_pow
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_Psi
import Theorems.Thm_Formalism_BaseCaseIdentities_Data_coeff_PsiPartial
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
theorem _root_.solution : D.PsiIsLimit := by
  intro t ht b A N hN
  rw [coeff_Psi, coeff_PsiPartial]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hN) fun j hj hj' => ?_
  rw [Finset.mem_Icc] at hj hj'
  have hlt : A.degree < D.l ^ j := by
    have h1 : j < D.l ^ j := Nat.lt_pow_self D.one_lt_l
    omega
  rw [(ht c).pow (D.l ^ j) A hlt, mul_zero]
end Formalism.BaseCaseIdentities.Data
