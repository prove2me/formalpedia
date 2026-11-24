-- Prove2me | solution 1 for Formalism.L2.Th1.F.POf.cW_rec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:51:58.517814+00:00
-- url     : https://prove2.me/submissions/305354b2-db4b-494e-ab12-915b5884ff15

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Theorems.Thm_Formalism_L2_Th1_F_POf_cW_eq
import Theorems.Thm_Formalism_L2_Th1_F_POf_cW_one

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
theorem _root_.solution (g2 g3 : K) (m : ℕ) (hm : 2 ≤ m) : cW g2 g3 (m + 2) =
    3 / ((2 * ((m + 2 : ℕ) : K) + 1) * (((m + 2 : ℕ) : K) - 3)) *
      ∑ a ∈ Finset.range (m + 1), cW g2 g3 (a + 1) * cW g2 g3 (m - a + 1) := by
  rw [cW_eq, if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j => cW g2 g3 (j + 2) * cW g2 g3 (m + 2 - (j + 2))) (m + 2 - 3)]
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  rw [Finset.sum_range_succ, Finset.sum_range_succ']
  simp only [Nat.sub_self, zero_add, cW_one, mul_zero, zero_mul, add_zero]
  have : t + 1 + 2 - 3 = t := by omega
  rw [this]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.mp hj
  congr 2
  omega
end Formalism.L2.Th1.F.POf
