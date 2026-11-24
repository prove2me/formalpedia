-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Fm_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:39:49.393958+00:00
-- url     : https://prove2.me/submissions/b53b6c0e-d5de-4fe0-a5de-d9d5e266e8c4

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {K θ β t : ℝ} (hK0 : 0 ≤ K) (hK1 : K ≤ 1) (hθ : |θ| ≤ 1) (hβ : 1 / 2 ≤ β) (hβ1 : β ≤ 1)
    (ht : 1 ≤ t) : |Fm K θ β t| ≤ 3 * t := by
  have hb : 0 < β := by linarith
  have htb : t ^ β ≤ t := by
    have := Real.rpow_le_rpow_of_exponent_le ht hβ1
    rwa [Real.rpow_one] at this
  have htpos : 0 ≤ t ^ β := Real.rpow_nonneg (by linarith) _
  unfold Fm
  rw [abs_mul, abs_of_nonneg hK0]
  have h3 : |θ * t ^ β / β| ≤ 2 * t := by
    rw [abs_div, abs_mul, abs_of_nonneg htpos, abs_of_pos hb, div_le_iff₀ hb]
    nlinarith [mul_le_mul_of_nonneg_right hθ htpos, abs_nonneg θ]
  have h2 : |t - θ * t ^ β / β| ≤ 3 * t := by
    calc |t - θ * t ^ β / β| ≤ |t| + |θ * t ^ β / β| := abs_sub _ _
      _ ≤ t + 2 * t := by rw [abs_of_nonneg (by linarith)]; linarith
      _ = 3 * t := by ring
  calc K * |t - θ * t ^ β / β| ≤ 1 * (3 * t) := mul_le_mul hK1 h2 (abs_nonneg _) (by norm_num)
    _ = 3 * t := one_mul _
end Formalism.HermitianLattices.Ext.PrimesInProgressions
