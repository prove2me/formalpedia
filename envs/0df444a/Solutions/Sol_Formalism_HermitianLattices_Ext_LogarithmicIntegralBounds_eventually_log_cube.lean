-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.eventually_log_cube
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:27.001831+00:00
-- url     : https://prove2.me/submissions/16150bf1-b137-42b7-b578-5ee7346048b9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (K a : ℝ) (hK : 0 < K) (ha : 0 < a) :
    ∃ x₂ : ℝ, ∀ x : ℝ, x₂ ≤ x → K * Real.log x ^ 3 ≤ x ^ a := by
  have h := (isLittleO_log_rpow_rpow_atTop 3 ha).bound (by positivity : (0 : ℝ) < 1 / K)
  obtain ⟨x₂, hx₂⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_gt_atTop 0))
  refine ⟨x₂, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx₂ x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos h2 a)] at h1
  have h3 : Real.log x ^ 3 = Real.log x ^ (3 : ℝ) := by
    rw [← Real.rpow_natCast]
    norm_num
  rw [h3]
  calc K * Real.log x ^ (3 : ℝ) ≤ K * |Real.log x ^ (3 : ℝ)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hK.le
    _ ≤ K * (1 / K * x ^ a) := mul_le_mul_of_nonneg_left h1 hK.le
    _ = x ^ a := by field_simp
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
