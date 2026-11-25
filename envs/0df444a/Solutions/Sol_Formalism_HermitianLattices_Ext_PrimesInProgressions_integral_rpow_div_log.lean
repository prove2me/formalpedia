-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.integral_rpow_div_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:54:16.818028+00:00
-- url     : https://prove2.me/submissions/e8a57e69-0d87-4847-8a04-0f7434ed498e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB
import Theorems.Thm_P2M_Formalism_HermitianLattices_Ext_PrimesInProgressions_intervalIntegrable_inv_log__5efe15a227a2

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
theorem _root_.solution {β X : ℝ} (hβ : 0 < β) (hX : 2 ≤ X) :
    ∫ t in (2 : ℝ)..X, t ^ (β - 1) / Real.log t = liX (X ^ β) - liX ((2 : ℝ) ^ β) := by
  have h1X : 1 < X ^ β := Real.one_lt_rpow (by linarith) hβ
  have h12 : 1 < (2 : ℝ) ^ β := Real.one_lt_rpow (by norm_num) hβ
  have hsub : liX (X ^ β) - liX ((2 : ℝ) ^ β) = ∫ u in ((2 : ℝ) ^ β)..(X ^ β), 1 / Real.log u := by
    unfold liX
    exact intervalIntegral.integral_interval_sub_left (intervalIntegrable_inv_log' (by norm_num) h1X)
      (intervalIntegrable_inv_log' (by norm_num) h12)
  rw [hsub]
  have key := intervalIntegral.integral_comp_mul_deriv' (a := 2) (b := X) (f := fun t : ℝ => t ^ β)
    (f' := fun t : ℝ => β * t ^ (β - 1)) (g := fun u : ℝ => 1 / Real.log u) ?_ ?_ ?_
  · rw [← key]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    simp only [Function.comp]
    rw [Real.log_rpow ht0]
    field_simp
  · intro t ht
    rw [Set.uIcc_of_le hX] at ht
    exact Real.hasDerivAt_rpow_const (Or.inl (by linarith [ht.1]))
  · intro t ht
    rw [Set.uIcc_of_le hX] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact (continuousAt_const.mul (Real.continuousAt_rpow_const t (β - 1) (Or.inl ht0))).continuousWithinAt
  · rintro u ⟨t, ht, rfl⟩
    rw [Set.uIcc_of_le hX] at ht
    have h1 : 1 < t ^ β := Real.one_lt_rpow (by linarith [ht.1]) hβ
    exact ((continuousAt_const).div (Real.continuousAt_log (by linarith)) (Real.log_pos h1).ne').continuousWithinAt
end Formalism.HermitianLattices.Ext.PrimesInProgressions
