-- Prove2me | solution 2 for Formalism.HermitianLattices.GL2PrimeSums.gl2a5s_le_small
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:33:18.476342+00:00
-- url     : https://prove2.me/submissions/72adf905-8913-436d-bd32-8f4ff4a1d334

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SmallPrimeFactorSumBound
import Theorems.Thm_Formalism_HermitianLattices_GL2PrimeSums_gl2a5s_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums
namespace Formalism.HermitianLattices.GL2PrimeSums
theorem _root_.solution {x : ℝ} (hx : 1 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) :
    primeTermWeight x N p ≤ Real.log x + 2 * Real.log p := by
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hfl : ⌊x⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
    omega
  have h := gl2a5s_le (by linarith : (0 : ℝ) ≤ x) N hp (Nat.log p ⌊x⌋₊)
  set a0 := Nat.log p ⌊x⌋₊
  have h1 : (a0 : ℝ) * Real.log p ≤ Real.log x := by
    rw [← Real.log_pow]
    apply Real.log_le_log (by positivity)
    have : p ^ a0 ≤ ⌊x⌋₊ := Nat.pow_log_le_self p hfl
    calc ((p : ℝ) ^ a0) = ((p ^ a0 : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast this
      _ ≤ x := Nat.floor_le (by linarith)
  have h2 : x / (p : ℝ) ^ (a0 + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : ⌊x⌋₊ < p ^ (a0 + 1) := Nat.lt_pow_succ_log_self hp.one_lt _
    have h3 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h4 : ((⌊x⌋₊ : ℝ) + 1) ≤ ((p ^ (a0 + 1) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at h4
    linarith
  have h5 : Real.log p * ((a0 : ℝ) + 2 * x / (p : ℝ) ^ (a0 + 1)) =
      (a0 : ℝ) * Real.log p + 2 * Real.log p * (x / (p : ℝ) ^ (a0 + 1)) := by ring
  have h6 : 2 * Real.log p * (x / (p : ℝ) ^ (a0 + 1)) ≤ 2 * Real.log p :=
    mul_le_of_le_one_right (by positivity) h2
  linarith
end Formalism.HermitianLattices.GL2PrimeSums
