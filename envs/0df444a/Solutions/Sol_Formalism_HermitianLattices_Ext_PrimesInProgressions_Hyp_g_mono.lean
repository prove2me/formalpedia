-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp.g_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:37:42.68092+00:00
-- url     : https://prove2.me/submissions/073e63c1-cf1d-46b2-81c5-ba24e14e7098

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_DHFinish2Of
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyperC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTDHHyper

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
open Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
theorem _root_.solution (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    (Real.log b + 1) / √b ≤ 2 * ((Real.log a + 1) / √a) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hL : 0 ≤ Real.log a := Real.log_nonneg ha
  have hsa : 0 < √a := Real.sqrt_pos.2 ha0
  have hsb : 0 < √b := Real.sqrt_pos.2 hb0
  set s := √b / √a with hs
  have hs1 : 1 ≤ s := by
    rw [hs, le_div_iff₀ hsa, one_mul]
    exact Real.sqrt_le_sqrt hab
  have hs0 : 0 < s := by linarith
  have hsb' : √b = √a * s := by
    rw [hs]
    field_simp
  have hb' : b = a * s ^ 2 := by
    rw [hs, div_pow, Real.sq_sqrt hb0.le, Real.sq_sqrt ha0.le]
    field_simp
  have hlogb : Real.log b = Real.log a + 2 * Real.log s := by
    rw [hb', Real.log_mul ha0.ne' (by positivity), Real.log_pow]
    push_cast
    ring
  have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  rw [hsb', hlogb, div_le_iff₀ (by positivity)]
  have e : 2 * ((Real.log a + 1) / √a) * (√a * s) = 2 * (Real.log a + 1) * s := by
    field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left hs1 hL]
end Formalism.HermitianLattices.Ext.PrimesInProgressions.Hyp
