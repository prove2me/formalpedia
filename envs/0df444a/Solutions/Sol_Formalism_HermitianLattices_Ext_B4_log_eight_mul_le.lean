-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.B4.log_eight_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:48.543202+00:00
-- url     : https://prove2.me/submissions/2523c9b6-28d3-4bd5-b0fb-24a457f5b934

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffFinal
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_LogEightBound_ProgTwo

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.B4
namespace Formalism.HermitianLattices.Ext.B4
theorem _root_.solution {M : ℕ} (hM : 3 ≤ M) : Real.log (2 * (M : ℝ) * ((2 : ℕ) + 2)) ≤ 3 * Real.log M := by
  have hMR : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have h8 : 2 * (M : ℝ) * ((2 : ℕ) + 2) = 8 * M := by push_cast; ring
  have h3 : 3 * Real.log M = Real.log ((M : ℝ) ^ 3) := by rw [Real.log_pow]; norm_num
  rw [h8, h3]
  apply Real.log_le_log (by positivity)
  have h9 : (9 : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
  have : (M : ℝ) ^ 3 = (M : ℝ) * (M : ℝ) ^ 2 := by ring
  rw [this]; nlinarith
end Formalism.HermitianLattices.Ext.B4
