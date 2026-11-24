-- Prove2me | solution 1 for Formalism.zetaPrimeSumErrorLipschitz
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:44:06.770908+00:00
-- url     : https://prove2.me/submissions/5527a775-1fb2-42f6-87f2-b9792a0d03cc

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Theorems.Thm_Formalism_LogFactorialMertensBounds_lipschitzConst_nonneg
import Theorems.Thm_Formalism_LogFactorialMertensBounds_lip_upto

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ArithmeticFunction
noncomputable section
open Formalism
open LogFactorialMertensBounds
namespace Formalism
theorem _root_.solution : GzLipschitz := by
  have hK := lipschitzConst_nonneg
  have hlip : ∀ a b : ℝ, 1 / 2 ≤ a → 1 / 2 ≤ b → |Gz a - Gz b| ≤ K0 * |a - b| := by
    intro a b ha hb
    exact lip_upto (⌊a⌋₊ + ⌊b⌋₊) b a hb
      (by push_cast; linarith [Nat.lt_floor_add_one b, Nat.cast_nonneg (α := ℝ) ⌊a⌋₊]) ha
      (by push_cast; linarith [Nat.lt_floor_add_one a, Nat.cast_nonneg (α := ℝ) ⌊b⌋₊])
  refine ⟨K0 + 2 * |Gz (1 / 2)|, fun t t' ht ht' => ⟨?_, ?_⟩⟩
  · have h := hlip t (1 / 2) ht le_rfl
    have h2 : |Gz t| ≤ |Gz t - Gz (1 / 2)| + |Gz (1 / 2)| := by
      have := abs_sub_abs_le_abs_sub (Gz t) (Gz (1 / 2))
      linarith
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ t - 1 / 2)] at h
    nlinarith [abs_nonneg (Gz (1 / 2)), mul_nonneg (abs_nonneg (Gz (1 / 2))) (by linarith : (0:ℝ) ≤ t - 1 / 2)]
  · exact le_trans (hlip t t' ht ht')
      (mul_le_mul_of_nonneg_right (by linarith [abs_nonneg (Gz (1 / 2))]) (abs_nonneg _))
end Formalism
