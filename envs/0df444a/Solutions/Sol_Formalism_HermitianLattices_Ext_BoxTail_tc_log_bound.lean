-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tc_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:51.583858+00:00
-- url     : https://prove2.me/submissions/28ba5354-1f3a-45b5-8582-b461d5ad51bb

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailKernel
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_PerronHorizontalSegmentBound
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailContourB

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution (Q : ℝ) (hQ : 2 ≤ Q) : Real.log (1 + 800 * (Q / 2)) ≤ 10 * Real.log Q := by
  have hQ0 : 0 < Q := by linarith
  have h1 : 1 + 800 * (Q / 2) ≤ Q ^ 10 := by
    have h9 : (2 : ℝ) ^ 9 * Q ≤ Q ^ 9 * Q :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hQ 9) hQ0.le
    have e : Q ^ 10 = Q ^ 9 * Q := by ring
    rw [e]
    norm_num at h9
    linarith
  calc Real.log (1 + 800 * (Q / 2)) ≤ Real.log (Q ^ 10) := Real.log_le_log (by positivity) h1
    _ = 10 * Real.log Q := by rw [Real.log_pow]; norm_num
end Formalism.HermitianLattices.Ext.BoxTail
