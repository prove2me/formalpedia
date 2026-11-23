-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.nlog_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:48:52.356898+00:00
-- url     : https://prove2.me/submissions/7c8721eb-3446-4425-8662-6a7372230a6c

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open Finset
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (p x B : ℕ) (hx : x ≤ B) : (Nat.log p x : ℝ) ≤ Real.logb p B := by
  rcases Nat.lt_or_ge p 2 with hp | hp
  · rw [Nat.log_of_left_le_one (by omega) x]
    interval_cases p <;> simp [Real.logb]
  · rcases Nat.eq_zero_or_pos x with rfl | hx0
    · rcases Nat.eq_zero_or_pos B with rfl | hB
      · simp
      · simp only [Nat.log_zero_right, Nat.cast_zero]
        exact Real.logb_nonneg (by exact_mod_cast hp) (by exact_mod_cast hB)
    · rw [Real.le_logb_iff_rpow_le (by exact_mod_cast hp)
        (by exact_mod_cast (lt_of_lt_of_le hx0 hx)), Real.rpow_natCast]
      exact_mod_cast (Nat.pow_log_le_self p hx0.ne').trans hx
end Formalism.GM.MeanGammaLemmas
