-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.exists_taylor_truncation_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T11:44:11.493101+00:00
-- url     : https://prove2.me/submissions/6ee1555e-1d5b-437e-af44-9741910aa4b6

import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_IteratedDerivLseriesAlternatingNonneg
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_BqKeyOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped ComplexOrder Nat
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution (T : ℝ) (hT : 1 ≤ T) :
    ∃ M : ℕ, 1 ≤ M ∧ T * (3 / 4 : ℝ) ^ M ≤ 1 ∧ (M : ℝ) ≤ Real.log T / Real.log (4 / 3) + 2 := by
  have hl43 : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have hT0 : 0 < T := by linarith
  have hx0 : 0 ≤ Real.log T / Real.log (4 / 3) := div_nonneg (Real.log_nonneg hT) hl43.le
  refine ⟨⌈Real.log T / Real.log (4 / 3)⌉₊ + 1, by omega, ?_, ?_⟩
  · have hM : Real.log T / Real.log (4 / 3) ≤ ((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) := by
      push_cast; linarith [Nat.le_ceil (Real.log T / Real.log (4 / 3))]
    have hlog : Real.log T ≤ ((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) * Real.log (4 / 3) := by
      have h := mul_le_mul_of_nonneg_right hM hl43.le
      rwa [div_mul_cancel₀ _ hl43.ne'] at h
    have hT' : T ≤ (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by
      calc T = Real.exp (Real.log T) := (Real.exp_log hT0).symm
        _ ≤ Real.exp (((⌈Real.log T / Real.log (4 / 3)⌉₊ + 1 : ℕ) : ℝ) * Real.log (4 / 3)) :=
          Real.exp_le_exp.mpr hlog
        _ = (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by
          rw [← Real.log_pow, Real.exp_log (by positivity)]
    have h34 : (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hp : 0 < (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) := by positivity
    calc T * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1)
        ≤ (4 / 3 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) * (3 / 4 : ℝ) ^ (⌈Real.log T / Real.log (4 / 3)⌉₊ + 1) :=
          mul_le_mul_of_nonneg_right hT' hp.le
      _ = 1 := h34
  · push_cast
    linarith [Nat.ceil_lt_add_one hx0]
end Formalism.ZeroFreeDirichlet
