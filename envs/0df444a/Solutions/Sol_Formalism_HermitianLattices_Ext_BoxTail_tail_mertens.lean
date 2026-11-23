-- Prove2me | solution 1 for Formalism.HermitianLattices.Ext.BoxTail.tail_mertens
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:27:44.994859+00:00
-- url     : https://prove2.me/submissions/8a697c76-6bc8-4a1b-acfe-8945b62f34b8

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_JacobiCharacterSums_TailMertens
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_mertens_psi
import Theorems.Thm_Formalism_HermitianLattices_Ext_BoxTail_tail_mertens_nat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.BoxTail
namespace Formalism.HermitianLattices.Ext.BoxTail
theorem _root_.solution : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 2 ≤ y →
    ∑ n ∈ Icc 1 ⌊y⌋₊, (Λ n : ℝ) / (n : ℝ) ≤ C * Real.log y := by
  have hc : 0 ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1:ℝ) ≤ 4)
    linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(Real.log 4 + 4) * (1 / Real.log 2 + 1),
    mul_nonneg hc (add_nonneg (one_div_nonneg.2 hl2.le) zero_le_one), ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  obtain ⟨M, hM⟩ : ∃ M, ⌊y⌋₊ = M + 1 :=
    ⟨⌊y⌋₊ - 1, by
      have : 1 ≤ ⌊y⌋₊ := Nat.le_floor (by push_cast; linarith)
      omega⟩
  rw [hM]
  have h1 := tail_mertens_nat M
  have hpsi := tail_mertens_psi (M + 1)
  push_cast at hpsi
  have hM1 : (0:ℝ) < (M:ℝ) + 1 := by positivity
  have hMy : (M:ℝ) + 1 ≤ y := by
    have := Nat.floor_le hy0
    rw [hM] at this
    push_cast at this
    exact this
  have hlogy : Real.log 2 ≤ Real.log y := Real.log_le_log (by norm_num) hy
  have hlogM : Real.log ((M:ℝ) + 1) ≤ Real.log y := Real.log_le_log hM1 hMy
  have hq : (∑ n ∈ Icc 1 (M + 1), (Λ n : ℝ)) / ((M:ℝ) + 1) ≤ Real.log 4 + 4 := by
    rw [div_le_iff₀ hM1]
    exact hpsi
  have hone : 1 ≤ Real.log y / Real.log 2 := by
    rw [le_div_iff₀ hl2]
    linarith
  calc _ ≤ (Real.log 4 + 4) + (Real.log 4 + 4) * Real.log y := by
        have := mul_le_mul_of_nonneg_left hlogM hc
        linarith
    _ ≤ (Real.log 4 + 4) * (Real.log y / Real.log 2) + (Real.log 4 + 4) * Real.log y := by
        have := mul_le_mul_of_nonneg_left hone hc
        linarith
    _ = (Real.log 4 + 4) * (1 / Real.log 2 + 1) * Real.log y := by
        field_simp
end Formalism.HermitianLattices.Ext.BoxTail
