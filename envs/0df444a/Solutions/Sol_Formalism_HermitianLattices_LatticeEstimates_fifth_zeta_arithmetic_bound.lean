-- Prove2me | solution 1 for Formalism.HermitianLattices.LatticeEstimates.fifth_zeta_arithmetic_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:43.146675+00:00
-- url     : https://prove2.me/submissions/d3a1b419-44d8-4834-baca-1de51d2b0405

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InverseNormLeOfIntegerInner
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Theorems.Thm_Formalism_HermitianLattices_LatticeEstimates_weight_positive_part_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.LatticeEstimates
open Finset MeasureTheory Matrix Real
open Formalism.HermitianLattices.TraceIntegrality
open Formalism.LogVandermondeBounds.flipTwoThree (Interlace B0 len)
open scoped ComplexOrder
namespace Formalism.HermitianLattices.LatticeEstimates
theorem _root_.solution : AntitoneWeightLogBoundExists := by
  intro C₀ hC
  refine ⟨Real.log C₀ / Real.log 2 + 4, ?_⟩
  intro κ lam v logT logNorm muStd mu hv hT hA hN hS hmu
  rcases Nat.eq_zero_or_pos κ with rfl | hκ
  · have w0 : wt (plus lam) = 0 := by simp [wt, plus]
    have p0 : plus lam 0 = 0 := by simp [plus]
    have z0 : MeanSquareWeightBound lam = 0 := by simp [MeanSquareWeightBound, w0, p0]
    rw [w0] at hmu ⊢
    rw [p0]
    rw [z0] at hS
    have : -(lam (Fin.last 0) : ℝ) * logT ≤ |(lam (Fin.last 0) : ℝ)| * logT :=
      mul_le_mul_of_nonneg_right (neg_le_abs _) hT
    simp at hmu this ⊢
    linarith
  · have hκ' : (1:ℝ) ≤ κ := by exact_mod_cast hκ
    have hk : (2:ℝ) ≤ (κ : ℝ) + 1 := by linarith
    have hw : (0:ℝ) ≤ (wt (plus lam) : ℝ) := by exact_mod_cast weight_positive_part_nonneg lam hA
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlk : Real.log 2 ≤ Real.log ((κ : ℝ) + 1) := Real.log_le_log (by norm_num) hk
    have hlv : 0 ≤ Real.log v := Real.log_nonneg hv
    have hlC : 0 ≤ Real.log C₀ := Real.log_nonneg hC
    have ekv : Real.log (((κ : ℝ) + 1) * v) = Real.log ((κ : ℝ) + 1) + Real.log v :=
      Real.log_mul (by positivity) (by positivity)
    have eN : Real.log (C₀ * ((κ : ℝ) + 1) ^ 3 * v ^ 2)
        = Real.log C₀ + 3 * Real.log ((κ : ℝ) + 1) + 2 * Real.log v := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow]; push_cast; ring
    have h1 : Real.log C₀ ≤ Real.log C₀ / Real.log 2 * Real.log (((κ : ℝ) + 1) * v) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left (by rw [ekv]; linarith) hlC
    have h2 : logNorm + Real.log ((κ : ℝ) + 1) ≤ (Real.log C₀ / Real.log 2 + 4) * Real.log (((κ : ℝ) + 1) * v) := by
      rw [eN] at hN
      have : (Real.log C₀ / Real.log 2 + 4) * Real.log (((κ : ℝ) + 1) * v)
        = Real.log C₀ / Real.log 2 * Real.log (((κ : ℝ) + 1) * v) + 4 * (Real.log ((κ : ℝ) + 1) + Real.log v) := by
        rw [← ekv]; ring
      rw [this]; linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hw
    have h4 : -(lam (Fin.last κ) : ℝ) * logT ≤ |(lam (Fin.last κ) : ℝ)| * logT :=
      mul_le_mul_of_nonneg_right (neg_le_abs _) hT
    unfold MeanSquareWeightBound at hS
    nlinarith
end Formalism.HermitianLattices.LatticeEstimates
