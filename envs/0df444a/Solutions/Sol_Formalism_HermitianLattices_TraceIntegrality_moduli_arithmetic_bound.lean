-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.moduli_arithmetic_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:42:29.764973+00:00
-- url     : https://prove2.me/submissions/cbadf8c1-78b9-4f68-a7d7-1597b2738c26

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
theorem _root_.solution : Ms_arith := by
  intro C₀ hC₀
  refine ⟨8 * Real.log C₀ + 31 + C₀, ?_⟩
  intro f N v T L logg R2 logh hf hN hv hT hL hg hlf hlN hlv hR2 hh
  have hfr : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hc : 0 ≤ Real.log C₀ := Real.log_nonneg hC₀
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hC0' : C₀ ≠ 0 := by positivity
  have hf' : (f : ℝ) ≠ 0 := by positivity
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hv' : v ≠ 0 := by positivity
  have hT' : T ≠ 0 := by positivity
  have hlogR : Real.log R2 = Real.log C₀ + Real.log f + 2 * Real.log N + 2 * Real.log v
      + 2 * Real.log T := by
    rw [hR2, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul hC0' hf', Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast; ring
  have hR2' : R2 ≠ 0 := by rw [hR2]; positivity
  have hlogCR : Real.log (C₀ * R2) = Real.log C₀ + Real.log R2 := Real.log_mul hC0' hR2'
  set c := Real.log C₀ with hcdef
  set lT := Real.log T with hlTdef
  set X := L + lT + logg with hX
  clear_value X c lT
  have hX1 : 1 ≤ X := by linarith
  have hcX : c ≤ c * X := by nlinarith
  have hA : Real.log R2 ≤ (c + 5) * X := by
    have : Real.log R2 ≤ c + 5 * X := by rw [hlogR]; linarith
    linarith
  have hB : Real.log (C₀ * R2) ≤ (2 * c + 5) * X := by
    rw [hlogCR]; linarith
  have hfN2 : 0 ≤ (f : ℝ) * (N : ℝ) ^ 2 := by positivity
  have hP : 0 ≤ (f : ℝ) * (N : ℝ) ^ 2 * X := by positivity

  have t1 : (N : ℝ) ^ 2 * (2 * f * Real.log (C₀ * R2)) ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) := by
    have := mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ 2 * ((f : ℝ) * (N : ℝ) ^ 2))
    linarith

  have t2 : 4 * f * N * ((N : ℝ) + 1) * (Real.log R2 / 2) ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5)) := by
    have h1 : 4 * f * N * ((N : ℝ) + 1) * (Real.log R2 / 2)
        ≤ 4 * f * N * ((N : ℝ) + 1) * ((c + 5) * X / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (N : ℝ) * ((N : ℝ) + 1) ≤ 2 * (N : ℝ) ^ 2 := by nlinarith
    have h3 : 0 ≤ 2 * (f : ℝ) * ((c + 5) * X) := by positivity
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    linarith

  have t3 : (f : ℝ) * N * lT ≤ (f : ℝ) * (N : ℝ) ^ 2 * lT := by
    have h2 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ (f : ℝ) * lT)
    linarith
  have t3' : (f : ℝ) * (N : ℝ) ^ 2 * lT ≤ (f : ℝ) * (N : ℝ) ^ 2 * X :=
    mul_le_mul_of_nonneg_left (by linarith) hfN2
  have t4 : C₀ * f * (N : ℝ) ^ 2 * logg ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * C₀ := by
    have := mul_le_mul_of_nonneg_left (by linarith : logg ≤ X)
      (by positivity : 0 ≤ C₀ * ((f : ℝ) * (N : ℝ) ^ 2))
    linarith
  have hsum : logh ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) + (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5))
        + ((f : ℝ) * (N : ℝ) ^ 2 * X + (f : ℝ) * (N : ℝ) ^ 2 * X * C₀) := by linarith
  calc logh ≤ (f : ℝ) * (N : ℝ) ^ 2 * X * (2 * (2 * c + 5)) + (f : ℝ) * (N : ℝ) ^ 2 * X * (4 * (c + 5))
        + ((f : ℝ) * (N : ℝ) ^ 2 * X + (f : ℝ) * (N : ℝ) ^ 2 * X * C₀) := hsum
    _ = (8 * c + 31 + C₀) * f * (N : ℝ) ^ 2 * X := by ring
end Formalism.HermitianLattices.TraceIntegrality
