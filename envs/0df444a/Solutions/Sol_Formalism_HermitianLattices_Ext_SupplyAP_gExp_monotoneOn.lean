-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.SupplyAP.gExp_monotoneOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:33.595457+00:00
-- url     : https://prove2.me/submissions/df7f1c94-b286-449b-adb3-a6a960344b4e

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffBase
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_ExceptionalCharacterBounds_EffAbel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace Formalism.HermitianLattices.Ext.SupplyAP
private theorem gExp_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt gExp (-(Real.exp t) / (Real.exp t - 1) ^ 2 - (-(1 / t ^ 2))) t := by
  have hE : Real.exp t - 1 ≠ 0 := by linarith [Real.add_one_le_exp t]
  have h1 : HasDerivAt (fun t => 1 / (Real.exp t - 1)) (-(Real.exp t) / (Real.exp t - 1) ^ 2) t := by
    have := (hasDerivAt_const t (1:ℝ)).div ((Real.hasDerivAt_exp t).sub_const 1) hE
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun t : ℝ => 1 / t) (-(1 / t ^ 2)) t := by
    have := (hasDerivAt_const t (1:ℝ)).div (hasDerivAt_id' t) ht.ne'
    exact this.congr_deriv (by ring)
  exact h1.sub h2
end Formalism.HermitianLattices.Ext.SupplyAP
end
end

set_option autoImplicit false
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.SupplyAP
namespace Formalism.HermitianLattices.Ext.SupplyAP
theorem _root_.solution : MonotoneOn gExp (Set.Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · intro t ht; exact (gExp_hasDerivAt ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    exact (gExp_hasDerivAt ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    have ht : 0 < t := ht
    rw [(gExp_hasDerivAt ht).deriv]
    have hE : 0 < Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
    set a := Real.exp (t / 2)
    set b := Real.exp (-(t / 2))
    have hab : a * b = 1 := by simp only [a, b]; rw [← Real.exp_add]; simp
    have haa : a * a = Real.exp t := by simp only [a]; rw [← Real.exp_add]; ring_nf
    have hs : t / 2 ≤ Real.sinh (t / 2) := Real.self_le_sinh_iff.mpr (by linarith)
    rw [Real.sinh_eq] at hs
    have hd : t ≤ a - b := by linarith
    have ha : 0 < a := Real.exp_pos _
    have key : Real.exp t * t ^ 2 ≤ (Real.exp t - 1) ^ 2 := by
      rw [← haa, ← hab]
      have : t ^ 2 ≤ (a - b) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (mul_self_nonneg a)]
    have : Real.exp t / (Real.exp t - 1) ^ 2 ≤ 1 / t ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    rw [neg_div]; linarith
end Formalism.HermitianLattices.Ext.SupplyAP
