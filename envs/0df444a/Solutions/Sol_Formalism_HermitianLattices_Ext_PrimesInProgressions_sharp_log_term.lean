-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.sharp_log_term
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:34:57.722647+00:00
-- url     : https://prove2.me/submissions/7103b032-d1ad-464c-a6c2-d42e66b5189a

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTEOf
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharpA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharpB
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTSharp

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
theorem _root_.solution {y δ : ℝ} (hy : 0 < y) (hδ : 0 < δ) :
    |y * ((1 + δ) / δ) * ((Real.log ((1 + δ) * y) - 1) - (Real.log y - 1)) - y| ≤ δ * y := by
  have h1 : (0 : ℝ) < 1 + δ := by linarith
  rw [Real.log_mul h1.ne' hy.ne']
  have hup : Real.log (1 + δ) ≤ δ := by
    have := Real.log_le_sub_one_of_pos h1; linarith
  have hlo : δ / (1 + δ) ≤ Real.log (1 + δ) := by
    have := Real.one_sub_inv_le_log_of_pos h1
    have e : 1 - (1 + δ)⁻¹ = δ / (1 + δ) := by field_simp; ring
    linarith
  have e : y * ((1 + δ) / δ) * ((Real.log (1 + δ) + Real.log y - 1) - (Real.log y - 1)) - y =
      y * ((1 + δ) / δ * Real.log (1 + δ) - 1) := by ring
  rw [e, abs_mul, abs_of_pos hy, mul_comm δ y]
  refine mul_le_mul_of_nonneg_left ?_ hy.le
  have hc : 0 < (1 + δ) / δ := by positivity
  rw [abs_le]
  constructor
  · have : (1 + δ) / δ * (δ / (1 + δ)) ≤ (1 + δ) / δ * Real.log (1 + δ) :=
      mul_le_mul_of_nonneg_left hlo hc.le
    have e2 : (1 + δ) / δ * (δ / (1 + δ)) = 1 := by field_simp
    linarith
  · have : (1 + δ) / δ * Real.log (1 + δ) ≤ (1 + δ) / δ * δ := mul_le_mul_of_nonneg_left hup hc.le
    have e2 : (1 + δ) / δ * δ = 1 + δ := by field_simp
    linarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
