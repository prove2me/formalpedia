-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:08:01.620873+00:00
-- url     : https://prove2.me/submissions/e5a696a4-66ee-4d60-b7f0-0c4c9f40611e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_Icc_one_eq_Ioc

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
theorem _root_.solution (u : ℕ → ℝ) (hu : ∀ n, 0 ≤ u n) (hu1 : ∀ n, u n ≤ 1) (T : ℕ) (B : ℝ)
    (hB : ∀ M, T ≤ M → ∑ n ∈ Ioc T M, u n ≤ B) (M : ℕ) : ∑ n ∈ Icc 1 M, u n ≤ T + B := by
  have hcard : ∀ K : ℕ, ∑ n ∈ Icc 1 K, u n ≤ K := fun K => by
    calc ∑ n ∈ Icc 1 K, u n ≤ ∑ n ∈ Icc 1 K, (1:ℝ) := Finset.sum_le_sum (fun n _ => hu1 n)
      _ = K := by simp
  have hB0 : 0 ≤ B := by simpa using hB T le_rfl
  rcases le_or_gt M T with h | h
  · have hMT : (M:ℝ) ≤ T := by exact_mod_cast h
    linarith [hcard M]
  · have h2 := hcard T
    rw [dA_Icc_one_eq_Ioc] at h2 ⊢
    rw [← Finset.sum_Ioc_consecutive u (Nat.zero_le T) h.le]
    linarith [hB M h.le]
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
