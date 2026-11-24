-- Prove2me | solution 1 for Formalism.LogFactorialMertensBounds.deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:36:47.551742+00:00
-- url     : https://prove2.me/submissions/a2147e0b-b33e-44c6-b32f-a1e31f608134

import Definitions.Def_Formalism_StatementU
import Definitions.Def_Formalism_ZetaNonvanishing_GzLipschitz
import Theorems.Thm_Formalism_LogFactorialMertensBounds_mertens_upper
import Theorems.Thm_Formalism_LogFactorialMertensBounds_mertens_lower

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
open Formalism.LogFactorialMertensBounds
namespace Formalism.LogFactorialMertensBounds
theorem _root_.solution (k : ℕ) (x : ℝ) (hx1 : (k:ℝ) ≤ x) (hx1' : 1 / 2 ≤ x) (hx2 : x ≤ k + 1) :
    |A k - Real.log x + Real.eulerMascheroniConstant| ≤ K0 := by
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hl4 := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)
  unfold K0
  rw [abs_le]
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have hA : A 0 = 0 := by simp [A]
    have hx1'' : x ≤ 1 := by simpa using hx2
    have hlx : Real.log x ≤ 0 := Real.log_nonpos (by linarith) hx1''
    have hlx2 : Real.log (1 / 2) ≤ Real.log x := Real.log_le_log (by norm_num) hx1'
    rw [one_div, Real.log_inv] at hlx2
    rw [hA]
    constructor <;> linarith
  · have hkR : (1:ℝ) ≤ k := by exact_mod_cast hk
    have hup := mertens_upper k hk
    have hlo := mertens_lower k hk
    have h1 : Real.log k ≤ Real.log x := Real.log_le_log (by linarith) hx1
    have h2 : Real.log x ≤ Real.log (2 * k) := Real.log_le_log (by linarith) (by linarith)
    rw [Real.log_mul two_ne_zero (by positivity)] at h2
    constructor <;> linarith
end Formalism.LogFactorialMertensBounds
