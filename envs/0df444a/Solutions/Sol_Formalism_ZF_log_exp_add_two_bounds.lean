-- Prove2me | solution 1 for Formalism.ZF.log_exp_add_two_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:09.3048+00:00
-- url     : https://prove2.me/submissions/a5dbfe05-5222-4a84-a109-6194b3dae964

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_NormIntegralComplLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZF
namespace Formalism.ZF
theorem _root_.solution (c s : ℝ) (hc : 0 < c) (hs : 8 / c ≤ s) :
    1 ≤ Real.exp (c * s / 4) ∧ 1 ≤ Real.log (Real.exp (c * s / 4) + 2) ∧
      Real.log (Real.exp (c * s / 4) + 2) ≤ c * s / 2 := by
  have hcs : 8 ≤ c * s := by
    rw [div_le_iff₀ hc] at hs
    linarith
  have hE1 : 1 ≤ Real.exp (c * s / 4) := Real.one_le_exp (by linarith)
  have hE2 : Real.exp 2 ≤ Real.exp (c * s / 4) := Real.exp_le_exp.mpr (by linarith)
  have he2 : (2 : ℝ) ≤ Real.exp 2 := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  refine ⟨hE1, ?_, ?_⟩
  · rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9
    linarith
  · rw [Real.log_le_iff_le_exp (by positivity)]
    have e : Real.exp (c * s / 2) = Real.exp (c * s / 4) ^ 2 := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [e]
    nlinarith
end Formalism.ZF
