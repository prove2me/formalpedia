-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.log_le_of_le_exp_log_conductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:44:12.615472+00:00
-- url     : https://prove2.me/submissions/0ab047a5-0fb5-4431-a51b-82ca09f379f7

import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LogTwoLeLogAnalyticConductor

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
theorem _root_.solution {A M L : ℝ} (hA : 1 ≤ A) (hM : 1 ≤ M) (hL : Real.log 2 ≤ L) (hX : 0 < Real.exp L)
    (hML : M ≤ 2 * A * Real.exp L) :
    Real.log M ≤ (Real.log (2 * A) / Real.log 2 + 1) * L := by
  have hA2 : 0 < 2 * A := by linarith
  have h1 : Real.log M ≤ Real.log (2 * A) + L := by
    have h := Real.log_le_log (by linarith) hML
    rwa [Real.log_mul hA2.ne' (Real.exp_pos L).ne', Real.log_exp] at h
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlA : 0 ≤ Real.log (2 * A) := Real.log_nonneg (by linarith)
  have h2 : Real.log (2 * A) ≤ Real.log (2 * A) / Real.log 2 * L := by
    have hq : 0 ≤ Real.log (2 * A) / Real.log 2 := div_nonneg hlA hl2.le
    calc Real.log (2 * A) = Real.log (2 * A) / Real.log 2 * Real.log 2 := by field_simp
      _ ≤ Real.log (2 * A) / Real.log 2 * L := mul_le_mul_of_nonneg_left hL hq
  rw [add_mul, one_mul]
  linarith
end Formalism.ZeroFreeDirichlet
