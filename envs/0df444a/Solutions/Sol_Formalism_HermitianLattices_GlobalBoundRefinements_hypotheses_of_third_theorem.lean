-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.hypotheses_of_third_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:02.782232+00:00
-- url     : https://prove2.me/submissions/2f749c3b-3a3b-4dbc-9197-5225183376e0

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
theorem _root_.solution : RankThresholdInequalityEventually := by
  intro C L f m k hC hL hf hm hme hmk r p q
  have hr3 : 3 ≤ r := by
    show 3 ≤ k + m - 1
    omega
  have hqr : q ≤ r := by
    show m / 2 ≤ k + m - 1
    omega
  have hpr : p ≤ r := by
    show k + m / 2 - 1 ≤ k + m - 1
    omega
  have hR3 : (3 : ℝ) ≤ r := by exact_mod_cast hr3
  have hR0 : (0 : ℝ) ≤ r := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h1 := Real.add_one_le_exp (r : ℝ)
    have h2 : Real.exp (-(r : ℝ)) * Real.exp r = 1 := by
      rw [← Real.exp_add]
      simp
    have h3 := Real.exp_pos (-(r : ℝ))
    nlinarith [mul_le_mul_of_nonneg_left h1 h3.le, mul_le_mul_of_nonneg_left hR3 h3.le]
  · obtain ⟨j, hj⟩ := hme
    show k + m / 2 - 1 + m / 2 = k + m - 1
    omega
  · show min (k + m / 2 - 1) (m / 2) = m / 2
    apply min_eq_right
    omega
  · have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    have hQ : (q : ℝ) ≤ r := by exact_mod_cast hqr
    have hpq : p * q ≤ r ^ 2 := by
      rw [sq]
      exact Nat.mul_le_mul hpr hqr
    have hPQ : ((p * q : ℕ) : ℝ) ≤ (r : ℝ) ^ 2 := by exact_mod_cast hpq
    have hPQ0 : (0 : ℝ) ≤ ((p * q : ℕ) : ℝ) := Nat.cast_nonneg _
    have hR1 : (1 : ℝ) ≤ r := by linarith
    have hlog0 : 0 ≤ Real.log r := Real.log_nonneg hR1
    have hlogr : Real.log r ≤ r := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < r)
      linarith
    have hf1 : (1 : ℝ) ≤ f := by exact_mod_cast hf
    have hp3 : ((p * q : ℕ) : ℝ) ^ 3 ≤ ((r : ℝ) ^ 2) ^ 3 := by
      first
      | exact pow_le_pow_left₀ hPQ0 hPQ 3
      | exact pow_le_pow_left hPQ0 hPQ 3
    have a1 : (q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 ≤ r * ((r : ℝ) ^ 2) ^ 3 :=
      mul_le_mul hQ hp3 (by positivity) hR0
    have a2 : (q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * r * Real.log r ≤ r * ((r : ℝ) ^ 2) ^ 3 * r * r := by
      apply mul_le_mul (mul_le_mul_of_nonneg_right a1 hR0) hlogr hlog0
      positivity
    have a3 : (r : ℝ) ^ 9 ≤ (r : ℝ) ^ 19 := by
      first
      | exact pow_le_pow_right₀ hR1 (by norm_num)
      | exact pow_le_pow_right hR1 (by norm_num)
    have hf5 : (1 : ℝ) ≤ (f : ℝ) ^ 5 := by
      first
      | exact one_le_pow₀ hf1
      | exact one_le_pow_of_one_le' hf1 5
    have a4 : (1 : ℝ) ≤ (f : ℝ) ^ 5 * L := by nlinarith
    have a5 : (r : ℝ) ^ 19 ≤ (r : ℝ) ^ 19 * ((f : ℝ) ^ 5 * L) :=
      le_mul_of_one_le_right (by positivity) a4
    have e1 : r * ((r : ℝ) ^ 2) ^ 3 * r * r = (r : ℝ) ^ 9 := by ring
    have hX : (q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * r * Real.log r ≤ (r : ℝ) ^ 19 * ((f : ℝ) ^ 5 * L) := by
      linarith
    have e2 : C * (q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * r * Real.log r / (1 / 3 : ℝ) ^ 2
        = 9 * C * ((q : ℝ) * ((p * q : ℕ) : ℝ) ^ 3 * r * Real.log r) := by ring
    rw [e2]
    have h9 := mul_le_mul_of_nonneg_left hX (by linarith : (0 : ℝ) ≤ 9 * C)
    linarith
end Formalism.HermitianLattices.GlobalBoundRefinements
