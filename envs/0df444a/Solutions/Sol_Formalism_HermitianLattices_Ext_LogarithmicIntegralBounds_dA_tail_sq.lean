-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_tail_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:27:31.801803+00:00
-- url     : https://prove2.me/submissions/c5d255f6-e431-4764-aff3-782b0e808f51

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
theorem _root_.solution (T : ℕ) (hT : 1 ≤ T) (M : ℕ) (hM : T ≤ M) :
    ∑ n ∈ Ioc T M, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / T - 1 / M := by
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hTM ih =>
    rw [Finset.sum_Ioc_succ_top hTM]
    have hM : (0:ℝ) < M := Nat.cast_pos.mpr (by omega)
    have e : 1 / (M:ℝ) - 1 / ((M:ℝ) + 1) = 1 / ((M:ℝ) * ((M:ℝ) + 1)) := by
      rw [div_sub_div _ _ hM.ne' (by positivity)]
      ring
    have k : 1 / ((M:ℝ) + 1) ^ 2 ≤ 1 / ((M:ℝ) * ((M:ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
    push_cast
    linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
