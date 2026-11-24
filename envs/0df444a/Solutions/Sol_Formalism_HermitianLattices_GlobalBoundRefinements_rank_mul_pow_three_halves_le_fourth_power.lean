-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.rank_mul_pow_three_halves_le_fourth_power
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:41.318796+00:00
-- url     : https://prove2.me/submissions/ebdbdc84-be2d-4bad-9e00-28058e913b74

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
namespace Formalism.HermitianLattices.GlobalBoundRefinements
theorem _root_.solution : RankMulPowThreeHalvesLeFourthPower := by
  intro f m k L hm hf hk hL
  have hqr : m / 2 ≤ k + m - 1 := by omega
  have hR1 : (1 : ℝ) ≤ ((k + m - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + m - 1)
  have hR0 : (0 : ℝ) ≤ ((k + m - 1 : ℕ) : ℝ) := by linarith
  have hQ0 : (0 : ℝ) ≤ ((m / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hQR : ((m / 2 : ℕ) : ℝ) ≤ ((k + m - 1 : ℕ) : ℝ) := by exact_mod_cast hqr
  have h1 : ((m / 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ ((k + m - 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) :=
    Real.rpow_le_rpow hQ0 hQR (by norm_num)
  have h2 : ((k + m - 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ ((k + m - 1 : ℕ) : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)
  rw [Real.rpow_two] at h2
  have h3 : ((k + m - 1 : ℕ) : ℝ) * ((k + m - 1 : ℕ) : ℝ) ^ 2 ≤ ((k + m - 1 : ℕ) : ℝ) ^ 19 := by
    have e : ((k + m - 1 : ℕ) : ℝ) * ((k + m - 1 : ℕ) : ℝ) ^ 2 = ((k + m - 1 : ℕ) : ℝ) ^ 3 := by ring
    rw [e]
    first
    | exact pow_le_pow_right₀ hR1 (by norm_num)
    | exact pow_le_pow_right hR1 (by norm_num)
  have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hf5 : (1 : ℝ) ≤ (f : ℝ) ^ 5 := by
    first
    | exact one_le_pow₀ hf1
    | exact one_le_pow_of_one_le' hf1 5
  have h4 : (1 : ℝ) ≤ (f : ℝ) ^ 5 * L := by nlinarith
  have h5 : ((k + m - 1 : ℕ) : ℝ) ^ 19 ≤ ((k + m - 1 : ℕ) : ℝ) ^ 19 * ((f : ℝ) ^ 5 * L) :=
    le_mul_of_one_le_right (by positivity) h4
  have h6 : ((k + m - 1 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
      ≤ ((k + m - 1 : ℕ) : ℝ) * ((k + m - 1 : ℕ) : ℝ) ^ 2 :=
    mul_le_mul_of_nonneg_left (h1.trans h2) hR0
  have h7 : ((k + m - 1 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
      ≤ ((k + m - 1 : ℕ) : ℝ) ^ 19 * ((f : ℝ) ^ 5 * L) := h6.trans (h3.trans h5)
  have h8 := mul_le_mul_of_nonneg_left h7 (by norm_num : (0 : ℝ) ≤ 120)
  calc 120 * ((k + m - 1 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)
      = 120 * (((k + m - 1 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := by ring
    _ ≤ 120 * (((k + m - 1 : ℕ) : ℝ) ^ 19 * ((f : ℝ) ^ 5 * L)) := h8
    _ = 120 * ((k + m - 1 : ℕ) : ℝ) ^ 19 * (f : ℝ) ^ 5 * L := by ring
end Formalism.HermitianLattices.GlobalBoundRefinements
