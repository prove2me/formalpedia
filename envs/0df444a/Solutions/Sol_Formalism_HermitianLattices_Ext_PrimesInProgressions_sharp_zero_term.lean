-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.sharp_zero_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:21:21.800157+00:00
-- url     : https://prove2.me/submissions/fbae38ca-a513-4c23-a11d-5440adc1f56b

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharpA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharpB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharp
import Theorems.Thm_Formalism_HermitianLattices_Ext_PrimesInProgressions_sharp_kernel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Complex Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {ρ : ℂ} (h1 : 1 / 2 ≤ ρ.re) (h2 : ρ.re < 1) {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    ‖((y * ((1 + δ) / δ) : ℝ) : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ‖ ≤ 2 * δ * y * y ^ (ρ.re - 1) := by
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at h1; norm_num at h1
  have hρ1 : ρ ≠ 1 := by
    intro h; rw [h] at h2; norm_num at h2
  have hs : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'
  have hpow : (y : ℂ) ^ ρ = (y : ℂ) * (y : ℂ) ^ (ρ - 1) := by
    rw [Complex.cpow_sub _ _ hyc, Complex.cpow_one]; field_simp
  have e : ((y * ((1 + δ) / δ) : ℝ) : ℂ) * ((((1 + δ) * y : ℝ) : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) -
        (y : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1))) - (y : ℂ) ^ ρ / ρ =
      (y : ℂ) ^ ρ / ρ *
        ((((1 + δ) / δ : ℝ) : ℂ) * ((((1 + δ : ℝ) : ℂ) ^ (ρ - 1) - 1) / (ρ - 1)) - 1) := by
    rw [Complex.ofReal_mul (1 + δ) y, Complex.mul_cpow_ofReal_nonneg (by linarith) hy.le, hpow]
    generalize ((1 + δ : ℝ) : ℂ) ^ (ρ - 1) = a
    generalize (y : ℂ) ^ (ρ - 1) = b
    push_cast
    field_simp
  rw [e, norm_mul, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hk := sharp_kernel hρ0 hρ1 h2.le hδ hδ2
  have hn : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  have hr : y ^ ρ.re = y * y ^ (ρ.re - 1) := by
    rw [Real.rpow_sub_one hy.ne']; field_simp
  calc y ^ ρ.re / ‖ρ‖ * _ ≤ y ^ ρ.re / ‖ρ‖ * (2 * δ * ‖ρ‖) :=
        mul_le_mul_of_nonneg_left hk (by positivity)
    _ = 2 * δ * y * y ^ (ρ.re - 1) := by rw [hr]; field_simp
end Formalism.HermitianLattices.Ext.PrimesInProgressions
