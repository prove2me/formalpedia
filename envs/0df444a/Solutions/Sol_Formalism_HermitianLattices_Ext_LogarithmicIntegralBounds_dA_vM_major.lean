-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_vM_major
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:33:13.700089+00:00
-- url     : https://prove2.me/submissions/94b00c6e-a81f-4403-bda4-b318c5b28727

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_sum_vM_le

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
theorem _root_.solution (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg : ∀ n, 1 ≤ n → g (n + 1) ≤ g n) (N : ℕ) :
    ∑ n ∈ Icc 1 N, vonMangoldt n * g n ≤ dA_KC * ∑ n ∈ Icc 1 N, g n := by
  have key : ∀ M : ℕ, (∑ n ∈ Icc 1 M, vonMangoldt n * g n) - (∑ n ∈ Icc 1 M, vonMangoldt n) * g M
      ≤ dA_KC * ((∑ n ∈ Icc 1 M, g n) - (M : ℝ) * g M) := by
    intro M
    induction M with
    | zero => simp [Finset.Icc_eq_empty_of_lt (show (0:ℕ) < 1 by norm_num)]
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega),
        Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega),
        Finset.sum_Icc_succ_top (show 1 ≤ M + 1 by omega)]
      have h1 : (∑ n ∈ Icc 1 M, vonMangoldt n) * (g M - g (M + 1))
          ≤ dA_KC * M * (g M - g (M + 1)) := by
        rcases Nat.eq_zero_or_pos M with h | h
        · subst h
          simp [Finset.Icc_eq_empty_of_lt (show (0:ℕ) < 1 by norm_num)]
        · exact mul_le_mul_of_nonneg_right (dA_sum_vM_le M) (by linarith [hg M h])
      push_cast
      linarith
  have h2 : (∑ n ∈ Icc 1 N, vonMangoldt n) * g N ≤ dA_KC * N * g N :=
    mul_le_mul_of_nonneg_right (dA_sum_vM_le N) (hg0 N)
  have h3 := key N
  linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
