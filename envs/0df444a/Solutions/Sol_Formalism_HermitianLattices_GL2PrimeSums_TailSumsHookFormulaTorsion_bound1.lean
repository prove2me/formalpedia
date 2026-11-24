-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.bound1
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:35.285142+00:00
-- url     : https://prove2.me/submissions/00338fcb-8134-4909-9c64-0886d82359f8

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
theorem _root_.solution (x Q : ℝ) (hx : 3 ≤ x) (hQ : 1 ≤ Q) :
    3 ≤ ⌊x ^ (400 : ℝ)⌋₊ ∧ ((⌊x ^ (400 : ℝ)⌋₊ : ℕ) : ℝ) ^ (-((1 : ℝ) / 400)) ≤ 2 / x ∧
      0 ≤ Real.log ((⌊x ^ (400 : ℝ)⌋₊ : ℕ) * Q) ∧
      Real.log ((⌊x ^ (400 : ℝ)⌋₊ : ℕ) * Q) ≤ 400 * Real.log x + Real.log Q := by
  have hx0 : 0 < x := by linarith
  set X := x ^ (400 : ℝ) with hX
  have hX3 : 3 ≤ X := by
    have : x ^ (1 : ℝ) ≤ x ^ (400 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hM3 : 3 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX3)
  have hMle : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hMgt : X < ((⌊X⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one X
  set M := ⌊X⌋₊
  have hM3' : (3 : ℝ) ≤ M := by exact_mod_cast hM3
  have hM0 : (0 : ℝ) < M := by linarith
  refine ⟨hM3, ?_, ?_, ?_⟩
  · have h1 : X / 2 ≤ M := by linarith
    have h2 : (M : ℝ) ^ (-((1 : ℝ) / 400)) ≤ (X / 2) ^ (-((1 : ℝ) / 400)) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) h1 (by norm_num)
    have h3 : (X / 2) ^ (-((1 : ℝ) / 400)) = X ^ (-((1 : ℝ) / 400)) / (2 : ℝ) ^ (-((1 : ℝ) / 400)) :=
      Real.div_rpow (by linarith) (by norm_num) _
    have h4 : X ^ (-((1 : ℝ) / 400)) = x⁻¹ := by
      rw [hX, ← Real.rpow_mul hx0.le, ← Real.rpow_neg_one]
      congr 1
      norm_num
    have h5 : (2 : ℝ)⁻¹ ≤ (2 : ℝ) ^ (-((1 : ℝ) / 400)) := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    rw [h3, h4] at h2
    refine h2.trans ?_
    rw [div_le_div_iff₀ (by positivity) hx0]
    have : x⁻¹ * x = 1 := inv_mul_cancel₀ hx0.ne'
    rw [this]
    linarith
  · apply Real.log_nonneg
    nlinarith
  · rw [Real.log_mul hM0.ne' (by linarith)]
    have h1 : Real.log (M : ℝ) ≤ Real.log X := Real.log_le_log hM0 hMle
    have h2 : Real.log X = 400 * Real.log x := by rw [hX, Real.log_rpow hx0]
    linarith
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
