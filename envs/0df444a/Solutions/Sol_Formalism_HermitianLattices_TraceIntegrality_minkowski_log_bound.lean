-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.minkowski_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:37.003633+00:00
-- url     : https://prove2.me/submissions/7e6eeec6-f6ab-42c8-8ee8-8db9d536c223

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_MinkowskiDivisorBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : Minkowski_log := by
  refine ⟨12, ?_⟩
  intro M hM
  have hMr : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hM0 : (0 : ℝ) < M := by linarith
  have hfac : (((4 * M).factorial : ℕ) : ℝ) ≤ ((4 * M : ℕ) : ℝ) ^ (4 * M) := by
    exact_mod_cast Nat.factorial_le_pow (4 * M)
  have hfpos : (0 : ℝ) < ((4 * M).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  have h1 : Real.log ((4 * M).factorial : ℝ) ≤ Real.log (((4 * M : ℕ) : ℝ) ^ (4 * M)) :=
    Real.log_le_log hfpos hfac
  have h2 : Real.log (((4 * M : ℕ) : ℝ) ^ (4 * M)) = (4 * (M : ℝ)) * (Real.log 4 + Real.log M) := by
    rw [Real.log_pow]
    push_cast
    rw [Real.log_mul (by norm_num) hM0.ne']
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h5 : Real.log 2 ≤ Real.log M := Real.log_le_log (by norm_num) hMr
  have h6 : Real.log 4 + Real.log M ≤ 3 * Real.log M := by linarith
  calc Real.log ((4 * M).factorial : ℝ) ≤ (4 * (M : ℝ)) * (Real.log 4 + Real.log M) := by
        rw [← h2]; exact h1
    _ ≤ (4 * (M : ℝ)) * (3 * Real.log M) := mul_le_mul_of_nonneg_left h6 (by linarith)
    _ = 12 * M * Real.log M := by ring
end Formalism.HermitianLattices.TraceIntegrality
