-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.dA_sum_min_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:35:08.755867+00:00
-- url     : https://prove2.me/submissions/2ff847f1-91e4-4ab5-987b-80e4872ff93c

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MeanSquareHypWIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqDiagA
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_sum_split
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_dA_tail_sq

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
theorem _root_.solution (x : ℝ) (hx : 1 ≤ x) (M : ℕ) :
    ∑ m ∈ Icc 1 M, min 1 (x / (m : ℝ) ^ 2) ≤ 3 * Real.sqrt x := by
  have hs1 : 1 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hx
    rwa [Real.sqrt_one] at h
  have hsx : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hT1 : 1 ≤ ⌊Real.sqrt x⌋₊ := Nat.le_floor (by rw [Nat.cast_one]; exact hs1)
  have hTgt : Real.sqrt x < (⌊Real.sqrt x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hTpos : (0:ℝ) < ⌊Real.sqrt x⌋₊ := Nat.cast_pos.mpr (by omega)
  have hT1' : (1:ℝ) ≤ ⌊Real.sqrt x⌋₊ := by exact_mod_cast hT1
  have h2T : Real.sqrt x ≤ 2 * (⌊Real.sqrt x⌋₊ : ℝ) := by linarith
  have htail : ∀ K, ⌊Real.sqrt x⌋₊ ≤ K →
      ∑ m ∈ Ioc ⌊Real.sqrt x⌋₊ K, min 1 (x / (m:ℝ) ^ 2) ≤ 2 * Real.sqrt x := by
    intro K hK
    have h1 := dA_tail_sq ⌊Real.sqrt x⌋₊ hT1 K hK
    have hK0 : (0:ℝ) ≤ 1 / (K:ℝ) := by positivity
    calc ∑ m ∈ Ioc ⌊Real.sqrt x⌋₊ K, min 1 (x / (m:ℝ) ^ 2)
        ≤ ∑ m ∈ Ioc ⌊Real.sqrt x⌋₊ K, x * (1 / (m:ℝ) ^ 2) :=
          Finset.sum_le_sum (fun m _ => (min_le_right _ _).trans (le_of_eq (by rw [mul_one_div])))
      _ = x * ∑ m ∈ Ioc ⌊Real.sqrt x⌋₊ K, 1 / (m:ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ x * (1 / (⌊Real.sqrt x⌋₊ : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ ≤ 2 * Real.sqrt x := by
          rw [mul_one_div, div_le_iff₀ hTpos]
          nlinarith [mul_le_mul_of_nonneg_left h2T (Real.sqrt_nonneg x)]
  have hs := dA_sum_split (fun m => min 1 (x / (m:ℝ) ^ 2))
    (fun m => le_min zero_le_one (div_nonneg (by linarith) (by positivity)))
    (fun m => min_le_left _ _) ⌊Real.sqrt x⌋₊ (2 * Real.sqrt x) htail M
  have hTle : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x := Nat.floor_le (Real.sqrt_nonneg x)
  linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
