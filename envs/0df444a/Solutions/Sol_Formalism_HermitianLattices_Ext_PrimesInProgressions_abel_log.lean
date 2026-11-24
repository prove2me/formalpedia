-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.PrimesInProgressions.abel_log
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:28:34.705289+00:00
-- url     : https://prove2.me/submissions/5b6ff24f-a682-4a65-a947-79748f457a89

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_MSqTwistC
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_PNTPiB

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.PrimesInProgressions
open Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds
namespace Formalism.HermitianLattices.Ext.PrimesInProgressions
theorem _root_.solution (c : ℕ → ℝ) (h0 : c 0 = 0) (h1 : c 1 = 0) {X : ℝ} (hX : 2 ≤ X) :
    ∑ n ∈ Icc 0 ⌊X⌋₊, (Real.log n)⁻¹ * c n = (∑ n ∈ Icc 0 ⌊X⌋₊, c n) / Real.log X +
      ∫ t in (2 : ℝ)..X, (∑ n ∈ Icc 0 ⌊t⌋₊, c n) / (t * Real.log t ^ 2) := by
  rw [sum_mul_eq_sub_integral_mul₁ c (f := fun n ↦ (Real.log n)⁻¹) h0 h1,
    ← intervalIntegral.integral_of_le hX]
  · have int_deriv (f : ℝ → ℝ) :
        ∫ u in (2 : ℝ)..X, deriv (fun x ↦ (Real.log x)⁻¹) u * f u =
        ∫ u in (2 : ℝ)..X, -(f u / (u * Real.log u ^ 2)) :=
      intervalIntegral.integral_congr fun u _ ↦ by simp [field]
    rw [int_deriv, intervalIntegral.integral_neg]
    ring
  · intro z ⟨_, _⟩
    have : z ≠ 0 := by linarith
    have : Real.log z ≠ 0 := by apply Real.log_ne_zero_of_pos_of_ne_one <;> linarith
    fun_prop
  · refine ContinuousOn.integrableOn_Icc fun z ⟨_, _⟩ ↦ ContinuousWithinAt.congr ?_
      (fun _ _ ↦ Real.deriv_inv_log_apply) Real.deriv_inv_log_apply
    have : z ≠ 0 := by linarith
    have : Real.log z ^ 2 ≠ 0 := by
      refine pow_ne_zero 2 <| Real.log_ne_zero_of_pos_of_ne_one ?_ ?_ <;> linarith
    exact ContinuousAt.continuousWithinAt <| by fun_prop
end Formalism.HermitianLattices.Ext.PrimesInProgressions
