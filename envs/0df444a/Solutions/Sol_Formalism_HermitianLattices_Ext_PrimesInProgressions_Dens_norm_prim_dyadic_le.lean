-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens.norm_prim_dyadic_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:16:21.687798+00:00
-- url     : https://prove2.me/submissions/31ac1ede-83ea-4f2e-9e4a-a858f91b4fab

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensSt
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDensPair

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Finset
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
open Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZD Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
theorem _root_.solution {U : ℕ} (hU : 1 ≤ U) {w : ℂ} (hw : 0 ≤ w.re) (ht : w.im ≠ 0) :
    ‖(((2 * U : ℕ) : ℂ) ^ (1 - w) - (U : ℂ) ^ (1 - w)) / (1 - w)‖ ≤
      3 * (U : ℝ) ^ (1 - w.re) / |w.im| := by
  have hU0 : (0 : ℝ) < U := by exact_mod_cast hU
  have hre : (1 - w).re = 1 - w.re := by simp
  have hP : 0 < (U : ℝ) ^ (1 - w.re) := Real.rpow_pos_of_pos hU0 _
  have h1 : ‖(U : ℂ) ^ (1 - w)‖ = (U : ℝ) ^ (1 - w.re) := by
    rw [norm_natCast_cpow_of_pos (by omega), hre]
  have h2 : ‖((2 * U : ℕ) : ℂ) ^ (1 - w)‖ ≤ 2 * (U : ℝ) ^ (1 - w.re) := by
    rw [norm_natCast_cpow_of_pos (by omega), hre]
    push_cast
    rw [Real.mul_rpow (by norm_num) hU0.le]
    refine mul_le_mul_of_nonneg_right ?_ hP.le
    calc (2 : ℝ) ^ (1 - w.re) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have h3 : |w.im| ≤ ‖1 - w‖ := by
    have := Complex.abs_im_le_norm (1 - w)
    simpa using this
  have ht0 : 0 < |w.im| := abs_pos.mpr ht
  rw [norm_div]
  refine div_le_div₀ (by positivity) ?_ ht0 h3
  refine (norm_sub_le _ _).trans ?_
  rw [h1]; linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Dens
