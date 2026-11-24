-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds.twist_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:46:39.417569+00:00
-- url     : https://prove2.me/submissions/720c488d-4d30-4b6e-a7d9-a00db3bd1326

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqOrth
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistA
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sum_jacobiSym_eq_sum_residueClass
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_cnt_add_small
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sum_small_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_sum_cnt_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_abs_jac_le
import Theorems.Thm_Formalism_HermitianLattices_Ext_LogarithmicIntegralBounds_main_le_two_pi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset Classical
noncomputable section
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
private theorem twist_decomposition_bound_of_sum_bounds (C : Finset ℕ) (J N S main : ℕ → ℝ) (k A B : ℝ)
    (hJ : ∀ b, |J b| ≤ 1) (hS0 : ∀ b, 0 ≤ S b)
    (hNb : ∀ b ∈ C, |N b + S b - main b| ≤ 2 * |k| * (N b + S b))
    (hMb : ∀ b ∈ C, |main b| ≤ 2 * (N b + S b))
    (hN : ∑ b ∈ C, N b ≤ A) (hS : ∑ b ∈ C, S b ≤ B) :
    |∑ b ∈ C, J b * N b - ∑ b ∈ C, J b * main b| ≤ 2 * |k| * (A + B) + B ∧
      ∑ b ∈ C, |main b| ≤ 2 * (A + B) := by
  have hk := abs_nonneg k
  constructor
  · rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have step : ∀ b ∈ C, |J b * N b - J b * main b| ≤ 2 * |k| * N b + (2 * |k| * S b + S b) := by
      intro b hb
      rw [← mul_sub, abs_mul]
      have h' := abs_le.mp (hNb b hb)
      have e : |N b - main b| ≤ 2 * |k| * N b + (2 * |k| * S b + S b) :=
        abs_le.mpr ⟨by linarith [h'.1, hS0 b], by linarith [h'.2, hS0 b]⟩
      calc |J b| * |N b - main b| ≤ 1 * |N b - main b| :=
            mul_le_mul_of_nonneg_right (hJ b) (abs_nonneg _)
        _ = |N b - main b| := one_mul _
        _ ≤ _ := e
    refine (Finset.sum_le_sum step).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hA := mul_le_mul_of_nonneg_left hN (by linarith : (0 : ℝ) ≤ 2 * |k|)
    have hB := mul_le_mul_of_nonneg_left hS (by linarith : (0 : ℝ) ≤ 2 * |k|)
    linarith
  · calc ∑ b ∈ C, |main b| ≤ ∑ b ∈ C, 2 * (N b + S b) := Finset.sum_le_sum hMb
      _ = 2 * (∑ b ∈ C, N b + ∑ b ∈ C, S b) := by rw [← Finset.mul_sum, Finset.sum_add_distrib]
      _ ≤ 2 * (A + B) := by linarith
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
end
end

set_option autoImplicit false
open Finset Classical
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
open Formalism.HermitianLattices.ZeroFreeRegionGL2
namespace Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
theorem _root_.solution (m₀ s a₀ : ℕ) (X : ℝ) (hm : 0 < m₀) (hs : 0 < s) (hX : 0 ≤ X)
    (main : ℕ → ℝ) (k : ℝ) (hk : |k| ≤ 1 / 2)
    (hb : ∀ b ∈ clsB m₀ s a₀, |(piAP X (m₀ * s) b : ℝ) - main b| ≤ k * main b) :
    |∑ q ∈ PPset m₀ a₀ X, (jacobiSym (q : ℤ) s : ℝ) -
        ∑ b ∈ clsB m₀ s a₀, (jacobiSym (b : ℤ) s : ℝ) * main b| ≤
      2 * |k| * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) + X ^ (1 / 2 : ℝ) ∧
    ∑ b ∈ clsB m₀ s a₀, |main b| ≤ 2 * (((PPset m₀ a₀ X).card : ℝ) + X ^ (1 / 2 : ℝ)) := by
  have hmain := twist_decomposition_bound_of_sum_bounds (clsB m₀ s a₀) (fun b => (jacobiSym (b : ℤ) s : ℝ))
    (fun b => (((PPset m₀ a₀ X).filter (fun q => q % (m₀ * s) = b)).card : ℝ))
    (fun b => (smallCnt X (m₀ * s) b : ℝ)) main k ((PPset m₀ a₀ X).card : ℝ) (X ^ (1 / 2 : ℝ))
    (fun b => abs_jac_le _ _) (fun b => Nat.cast_nonneg _)
    (fun b hbC => by
      have h := (main_le_two_pi (Nat.cast_nonneg _) hk (hb b hbC)).2
      rw [← cnt_add_small m₀ s a₀ X b hbC] at h
      push_cast at h
      exact h)
    (fun b hbC => by
      have h := (main_le_two_pi (Nat.cast_nonneg _) hk (hb b hbC)).1
      rw [← cnt_add_small m₀ s a₀ X b hbC] at h
      push_cast at h
      exact h)
    (sum_cnt_le m₀ s a₀ X) (sum_small_le m₀ s a₀ X hX)
  rw [sum_jacobiSym_eq_sum_residueClass m₀ s a₀ X hm hs]
  exact hmain
end Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
