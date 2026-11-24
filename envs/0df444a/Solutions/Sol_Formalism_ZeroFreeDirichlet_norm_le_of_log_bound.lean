-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.norm_le_of_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:45:10.4915+00:00
-- url     : https://prove2.me/submissions/150f27f8-402f-44f9-b148-19b10f36da67

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
theorem _root_.solution {z : ℂ} {CL : ℝ} (q : ℕ) [NeZero q] (h : ‖z‖ ≤ CL * Real.log (3 * q)) :
    ‖z‖ ≤ |CL| * (3 * q) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h3 : (0 : ℝ) ≤ 3 * q := by positivity
  have hl0 : 0 ≤ Real.log (3 * q) := Real.log_nonneg (by linarith)
  have hl : Real.log (3 * q) ≤ 3 * q := Real.log_le_self h3
  calc ‖z‖ ≤ CL * Real.log (3 * q) := h
    _ ≤ |CL| * Real.log (3 * q) := mul_le_mul_of_nonneg_right (le_abs_self CL) hl0
    _ ≤ |CL| * (3 * q) := mul_le_mul_of_nonneg_left hl (abs_nonneg CL)
end Formalism.ZeroFreeDirichlet
