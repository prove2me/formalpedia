-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.bound2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:35.587799+00:00
-- url     : https://prove2.me/submissions/a818c84b-8d6a-4ef3-8fbc-88db2cf757c2

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
theorem _root_.solution (L : ℝ) (hL : 3 ≤ L) :
    3 ≤ ⌈L ^ 800⌉₊ ∧ ((⌈L ^ 800⌉₊ : ℕ) : ℝ) ^ (-((1 : ℝ) / 400)) ≤ 1 / L ^ 2 ∧
      Real.log ((⌈L ^ 800⌉₊ : ℕ) : ℝ) ≤ 1 + 800 * Real.log L := by
  have hL0 : 0 < L := by linarith
  have hY : 3 ≤ L ^ 800 := by
    have : L ^ 1 ≤ L ^ 800 := pow_le_pow_right₀ (by linarith) (by norm_num)
    rw [pow_one] at this
    linarith
  have h1 : L ^ 800 ≤ ((⌈L ^ 800⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have h2 : ((⌈L ^ 800⌉₊ : ℕ) : ℝ) < L ^ 800 + 1 := Nat.ceil_lt_add_one (by positivity)
  set M := ⌈L ^ 800⌉₊
  have hM3' : (3 : ℝ) ≤ M := by linarith
  refine ⟨by exact_mod_cast hM3', ?_, ?_⟩
  · have h3 : (M : ℝ) ^ (-((1 : ℝ) / 400)) ≤ (L ^ 800) ^ (-((1 : ℝ) / 400)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by norm_num)
    have h4 : (L ^ 800) ^ (-((1 : ℝ) / 400)) = 1 / L ^ 2 := by
      rw [one_div (L ^ 2), ← Real.rpow_natCast L 800, ← Real.rpow_mul hL0.le, ← Real.rpow_natCast L 2,
        ← Real.rpow_neg hL0.le]
      congr 1
      norm_num
    linarith
  · have h3 : (M : ℝ) ≤ 2 * L ^ 800 := by linarith
    have h4 : Real.log (M : ℝ) ≤ Real.log (2 * L ^ 800) := Real.log_le_log (by linarith) h3
    have h5 : Real.log (2 * L ^ 800) = Real.log 2 + 800 * Real.log L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    have h6 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    linarith
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
