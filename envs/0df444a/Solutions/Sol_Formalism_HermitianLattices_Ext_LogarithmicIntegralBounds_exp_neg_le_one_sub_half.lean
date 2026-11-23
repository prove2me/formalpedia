-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.exp_neg_le_one_sub_half
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:12.679531+00:00
-- url     : https://prove2.me/submissions/9855706b-f1ea-4682-9404-ea95a9374572

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_LandauZeroFreeBounds_LogDerivRegionChiOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount

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
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : Real.exp (-w) ≤ 1 - w / 2 := by
  have he1 : Real.exp (-1) ≤ 1 / 2 := by
    have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hm : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-1)]
  have hx : (1 - w) • (0:ℝ) + w • (-1:ℝ) = -w := by simp [smul_eq_mul]
  have hconv := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-1:ℝ))
    (by linarith : (0:ℝ) ≤ 1 - w) h0 (by ring : (1 - w) + w = 1)
  rw [hx, smul_eq_mul, smul_eq_mul, Real.exp_zero] at hconv
  nlinarith [mul_le_mul_of_nonneg_left he1 h0]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
