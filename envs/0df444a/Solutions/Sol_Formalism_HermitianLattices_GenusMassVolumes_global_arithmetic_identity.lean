-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.global_arithmetic_identity
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:34:41.9388+00:00
-- url     : https://prove2.me/submissions/fabb404d-6a97-4062-b4f5-0272aae2b441

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_InertPrimeCountBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_FiniteEulerProductLeZeta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset
open Formalism.LogVandermondeBounds.StandardLattice
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : GlobalArithmeticIdentity := by
  intro f M v Lv hM hv hL
  show ((((2 * Real.pi) ^ M / ((M - 1).factorial : ℝ)) ^ f * ((2 * v) ^ f) ^ ((1 : ℝ) / 2 - M) / Lv)⁻¹ =
    (((M - 1).factorial : ℝ) * (v / Real.pi) ^ M) ^ f / Real.sqrt ((2 * v) ^ f) * Lv)
  have hd : (0 : ℝ) < (2 * v) ^ f := by positivity
  rw [Real.rpow_sub hd, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hs : 0 < Real.sqrt ((2 * v) ^ f) := Real.sqrt_pos.2 hd
  have hfac : (0 : ℝ) < ((M - 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hpi := Real.pi_pos
  have key : ((2 * v) ^ f) ^ M = ((2 * Real.pi) ^ M / ((M - 1).factorial : ℝ)) ^ f *
      (((M - 1).factorial : ℝ) * (v / Real.pi) ^ M) ^ f := by
    rw [← pow_mul, mul_comm f M, pow_mul, ← mul_pow]
    congr 1
    rw [div_pow]
    field_simp
    ring
  rw [key]
  have hA : (0 : ℝ) < (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ) := by positivity
  have hB : (0 : ℝ) < ((M - 1).factorial : ℝ) * (v / Real.pi) ^ M := by positivity
  generalize (2 * Real.pi) ^ M / ((M - 1).factorial : ℝ) = A at hA ⊢
  generalize ((M - 1).factorial : ℝ) * (v / Real.pi) ^ M = B at hB ⊢
  have hAf : 0 < A ^ f := pow_pos hA f
  have hBf : 0 < B ^ f := pow_pos hB f
  field_simp
end Formalism.HermitianLattices.GenusMassVolumes
