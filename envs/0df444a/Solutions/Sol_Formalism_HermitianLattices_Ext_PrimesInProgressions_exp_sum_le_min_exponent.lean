-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.exp_sum_le_min_exponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:31:30.150498+00:00
-- url     : https://prove2.me/submissions/69f0e946-c61b-41de-8a7f-51ae207a8503

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiA
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiC

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
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds Formalism.ZeroFreeDirichlet ArithmeticFunction
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution {c l L u : ℝ} (hc : 0 < c) (hl : 0 < l) (hL : 0 ≤ L) (hu : L / 2 ≤ u) :
    Real.exp (-(c * u / l)) + Real.exp (-(c * Real.sqrt u)) ≤
      Real.exp (-(min (c / 2) (c ^ 2 / 2) * L / l)) + Real.exp (-Real.sqrt (min (c / 2) (c ^ 2 / 2) * L)) := by
  have hu0 : 0 ≤ u := by linarith
  have hm1 : min (c / 2) (c ^ 2 / 2) ≤ c / 2 := min_le_left _ _
  have hm2 : min (c / 2) (c ^ 2 / 2) ≤ c ^ 2 / 2 := min_le_right _ _
  have hm0 : 0 ≤ min (c / 2) (c ^ 2 / 2) := le_min (by positivity) (by positivity)
  apply add_le_add
  · apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    apply div_le_div_of_nonneg_right _ hl.le
    have h1 := mul_le_mul_of_nonneg_right hm1 hL
    nlinarith
  · apply Real.exp_le_exp.mpr
    rw [neg_le_neg_iff]
    rw [show c * Real.sqrt u = Real.sqrt (c ^ 2 * u) by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]]
    apply Real.sqrt_le_sqrt
    have h1 := mul_le_mul_of_nonneg_right hm2 hL
    nlinarith
end Formalism.HermitianLattices.Ext.PrimesInProgressions
