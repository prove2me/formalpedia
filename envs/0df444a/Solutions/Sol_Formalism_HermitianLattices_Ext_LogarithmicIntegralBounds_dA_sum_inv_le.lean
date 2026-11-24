-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_inv_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:34:22.72286+00:00
-- url     : https://prove2.me/submissions/4fdd9990-4ce3-4fda-ba01-91ad8eac357f

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA

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
open ArithmeticFunction (vonMangoldt)
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (N : ℕ) (hN : 1 ≤ N) : ∑ n ∈ Icc 1 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
  induction N with
  | zero => omega
  | succ M ih =>
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h
      simp
    · rw [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega)]
      have ih' := ih (by omega)
      have hM : (0:ℝ) < M := Nat.cast_pos.mpr h
      have hM1 : (M:ℝ) + 1 ≠ 0 := by positivity
      have hlog : Real.log ((M:ℝ) / ((M:ℝ) + 1)) ≤ (M:ℝ) / ((M:ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div hM.ne' hM1] at hlog
      have e : (M:ℝ) / ((M:ℝ) + 1) - 1 = -(1 / ((M:ℝ) + 1)) := by
        rw [div_sub_one hM1]
        ring
      push_cast
      linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
