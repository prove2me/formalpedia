-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.log_mul_abs_two_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:43:55.606907+00:00
-- url     : https://prove2.me/submissions/1bd8702d-fd0d-408d-98a4-e49a717ad95e

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_RealLargeTOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ 2 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have ht := abs_nonneg t
  have e : 2 * Real.log ((q : ℝ) * (|t| + 2)) = Real.log (((q : ℝ) * (|t| + 2)) ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [abs_mul, abs_two, e]
  apply Real.log_le_log (by positivity)
  have h1 : (q : ℝ) * (2 * |t| + 2) ≤ (q : ℝ) * (|t| + 2) ^ 2 :=
    mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  have h2 : (q : ℝ) * (|t| + 2) ^ 2 ≤ ((q : ℝ) * (|t| + 2)) ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
  linarith
end Formalism.ZeroFreeDirichlet
