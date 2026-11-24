-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.ev_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:35.775986+00:00
-- url     : https://prove2.me/submissions/98a16b5f-ffe1-4162-9cdd-2f26fc1aa262

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
namespace Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
theorem _root_.solution (p C₁ c₁ : ℝ) (hc₁ : 0 < c₁) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      L ^ p * (C₁ * (4 * L ^ 8 * Real.exp (-L) + 384 / c₁ ^ 4 * Real.exp (-(c₁ / 2 * L)))) ≤ 1 / 6 := by
  have T1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (p + 8) 1 one_pos
  have T2 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p (c₁ / 2) (by positivity)
  have T := ((T1.const_mul 4).add (T2.const_mul (384 / c₁ ^ 4))).const_mul C₁
  simp only [mul_zero, add_zero] at T
  have E := T.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 6)
  have E2 := E.and (eventually_gt_atTop (0 : ℝ))
  obtain ⟨L₀, h⟩ := eventually_atTop.mp E2
  refine ⟨L₀, fun L hL => ?_⟩
  obtain ⟨h1, h2⟩ := h L hL
  refine le_trans (le_of_eq ?_) h1
  rw [Real.rpow_add h2, show ((8 : ℝ)) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have e1 : -1 * L = -L := by ring
  have e2 : -(c₁ / 2) * L = -(c₁ / 2 * L) := by ring
  rw [e1, e2]
  ring
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
