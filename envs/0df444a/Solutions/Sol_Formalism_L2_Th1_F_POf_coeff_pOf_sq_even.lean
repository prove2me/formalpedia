-- Prove2me | solution 1 for Formalism.L2.Th1.F.POf.coeff_pOf_sq_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:35:15.607996+00:00
-- url     : https://prove2.me/submissions/a3d9ccc3-bd6f-4bf7-9ad4-2631ca55b8e7

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_EisensteinS2LimitFormula
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_Taylor
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_TaylorWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_AnalyticIdentityTheorems_WeierstrassNumeratorDenominator
import Theorems.Thm_Formalism_L2_Th1_F_POf_coeff_pOf
import Theorems.Thm_Formalism_L2_Th1_F_POf_sum_even_range

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
theorem _root_.solution (g2 g3 : K) (m : ℕ) :
    coeff (2 * m) (pOf g2 g3 ^ 2)
      = ∑ a ∈ Finset.range (m + 1), cW g2 g3 (a + 1) * cW g2 g3 (m - a + 1) := by
  rw [sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    ← sum_even_range (fun a => cW g2 g3 (a + 1) * cW g2 g3 (m - a + 1))]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  simp only [coeff_pOf]
  by_cases he : Even i
  · have he' : Even (2 * m - i) := by
      obtain ⟨a, rfl⟩ := he
      exact ⟨m - a, by omega⟩
    have : (2 * m - i) / 2 = m - i / 2 := by
      obtain ⟨a, rfl⟩ := he
      omega
    rw [if_pos he, if_pos he', if_pos he, this]
  · rw [if_neg he, if_neg he, zero_mul]
end Formalism.L2.Th1.F.POf
