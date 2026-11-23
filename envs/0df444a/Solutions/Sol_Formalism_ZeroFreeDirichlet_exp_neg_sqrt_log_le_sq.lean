-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.exp_neg_sqrt_log_le_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:09.742164+00:00
-- url     : https://prove2.me/submissions/f5ba88f4-b5f9-4881-8d65-780e9794da85

import Mathlib
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_AbsZeroTermSecondDifferenceLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution {cs c₀ y z : ℝ} (hc0 : 0 ≤ c₀) (hcs : c₀ ≤ cs) (hy : 1 ≤ y) (hyz : y ≤ z) :
    Real.exp (-cs * Real.sqrt (Real.log z)) ≤ Real.exp (-(c₀ / 2) * Real.sqrt (Real.log y)) ^ 2 := by
  have hlyz : Real.log y ≤ Real.log z := Real.log_le_log (by linarith) hyz
  have hs : Real.sqrt (Real.log y) ≤ Real.sqrt (Real.log z) := Real.sqrt_le_sqrt hlyz
  rw [sq, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_le_mul hcs hs (Real.sqrt_nonneg _) (le_trans hc0 hcs)]
end Formalism.ZeroFreeDirichlet
