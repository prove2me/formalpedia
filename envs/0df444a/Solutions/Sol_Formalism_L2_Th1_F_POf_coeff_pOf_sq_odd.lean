-- Prove2me | solution 1 for Formalism.L2.Th1.F.POf.coeff_pOf_sq_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:35:16.790858+00:00
-- url     : https://prove2.me/submissions/ff69200e-6225-45b9-845a-35489b2191ef

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Theorems.Thm_Formalism_L2_Th1_F_POf_coeff_pOf
import Theorems.Thm_Formalism_ELL_FormalGroupPointsParam_Ev_add
import Theorems.Thm_Formalism_L2_Th1_F_TaylorWp_T_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.Th1.CM (cW wpNum wpDen)
open PowerSeries
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.F Formalism.L2.Th1.F.POf
variable {K : Type} [Field K]
namespace Formalism.L2.Th1.F.POf
theorem _root_.solution (g2 g3 : K) (n : ℕ) (hn : ¬ Even n) :
    coeff n (pOf g2 g3 ^ 2) = 0 := by
  rw [sq, coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  simp only [coeff_pOf]
  by_cases he : Even p.1
  · have : ¬ Even p.2 := fun h2 => hn (hp' ▸ he.add h2)
    rw [if_neg this, mul_zero]
  · rw [if_neg he, zero_mul]
end Formalism.L2.Th1.F.POf
