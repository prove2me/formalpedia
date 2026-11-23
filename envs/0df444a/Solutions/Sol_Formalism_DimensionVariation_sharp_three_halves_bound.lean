-- Prove2me | solution 1 for Formalism.DimensionVariation.sharp_three_halves_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:15:16.647329+00:00
-- url     : https://prove2.me/submissions/609e5fb0-7410-47fd-b2a4-f829ba596390

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementCB
import Definitions.Def_Formalism_ThetaSupremumBounds_DivIneqRecordTwoConst6
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_DescendedNorm
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_PerEmbeddingCoupledBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset NumberField
open scoped Real
open Formalism Formalism.DimensionVariation
open Formalism.LatticeIndexTer (ph)
open Formalism.DivisionValues (fnorm chainFun chainMat)
open CB
namespace Formalism.DimensionVariation
theorem _root_.solution : LiftedMapEmbeddingLogBound := by
  intro J Pl Emb _ r ν n g0 Ksq kc Om th0sq nn nn' hcl hcl' v hν hK0 hkc hOm hth hnn hnn' hcl0 hcl0' hv
    hK j s
  have hterm : ∀ τ, Real.log ((Om τ s)⁻¹ ^ n j τ *
          (Real.exp 1 * (2 * (n j τ : ℝ) + 2) ^ (2 * g0 j) * Real.exp (∑ i, ph (ν j τ i)))) =
      (∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * Real.log (Om τ s) +
        (1 + 2 * (g0 j : ℝ) * Real.log (2 * (∑ i, ν j τ i) + 2)) := by
    intro τ
    have hO := hOm τ s
    have hB : (0 : ℝ) < 2 * (n j τ : ℝ) + 2 := by positivity
    rw [Real.log_mul (pow_ne_zero _ (inv_ne_zero hO.ne')) (by positivity),
      Real.log_mul (by positivity) (Real.exp_ne_zero _),
      Real.log_mul (Real.exp_ne_zero _) (pow_ne_zero _ hB.ne'), Real.log_pow, Real.log_inv,
      Real.log_exp, Real.log_pow, Real.log_exp, hν j τ]
    push_cast
    ring
  have hPpos : ∀ τ, 0 < ((Om τ s)⁻¹ ^ n j τ *
          (Real.exp 1 * (2 * (n j τ : ℝ) + 2) ^ (2 * g0 j) * Real.exp (∑ i, ph (ν j τ i)))) := fun τ =>
    mul_pos (pow_pos (inv_pos.mpr (hOm τ s)) _) (by positivity)
  have hlogP : Real.log (∏ τ, ((Om τ s)⁻¹ ^ n j τ *
          (Real.exp 1 * (2 * (n j τ : ℝ) + 2) ^ (2 * g0 j) * Real.exp (∑ i, ph (ν j τ i))))) =
      ∑ τ, ((∑ i, ph (ν j τ i)) - (∑ i, ν j τ i) * Real.log (Om τ s) +
        (1 + 2 * (g0 j : ℝ) * Real.log (2 * (∑ i, ν j τ i) + 2))) := by
    rw [Real.log_prod (fun τ _ => (hPpos τ).ne')]
    exact Finset.sum_congr rfl (fun τ _ => hterm τ)
  have h8 : (0 : ℝ) < 8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v := by
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) (Fintype.card Pl * g0 j)) hv.le
    linarith
  have hXpos : 0 < (kc j s ^ 2 * (8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ^ (Fintype.card Pl * g0 j) *
          th0sq s ^ (Fintype.card Pl * g0 j)) :=
    mul_pos (mul_pos (pow_pos (hkc j s) 2) (pow_pos h8 _)) (pow_pos (hth s) _)
  have hlogX : Real.log (kc j s ^ 2 * (8 + 32 * ((Fintype.card Pl * g0 j : ℕ) : ℝ) * v) ^ (Fintype.card Pl * g0 j) *
          th0sq s ^ (Fintype.card Pl * g0 j)) =
      2 * Real.log (kc j s) +
        (Fintype.card Pl : ℝ) * g0 j * Real.log (8 + 32 * ((Fintype.card Pl : ℝ) * g0 j) * v) +
        (Fintype.card Pl : ℝ) * g0 j * Real.log (th0sq s) := by
    rw [Real.log_mul (mul_pos (pow_pos (hkc j s) 2) (pow_pos h8 _)).ne' (pow_pos (hth s) _).ne',
      Real.log_mul (pow_pos (hkc j s) 2).ne' (pow_pos h8 _).ne', Real.log_pow, Real.log_pow,
      Real.log_pow]
    push_cast
    ring
  have hPP : 0 < ∏ τ, ((Om τ s)⁻¹ ^ n j τ *
          (Real.exp 1 * (2 * (n j τ : ℝ) + 2) ^ (2 * g0 j) * Real.exp (∑ i, ph (ν j τ i)))) := Finset.prod_pos (fun τ _ => hPpos τ)
  have hK1 := hK j s
  unfold cbSq at hK1
  have hl := Real.log_le_log (hK0 j s) hK1
  rw [Real.log_mul (mul_pos (mul_pos (hnn j) (hnn' j)) (mul_pos (hcl0 j) (hcl0' j))).ne'
      (mul_pos hXpos hPP).ne',
    Real.log_mul (mul_pos (hnn j) (hnn' j)).ne' (mul_pos (hcl0 j) (hcl0' j)).ne',
    Real.log_mul (hnn j).ne' (hnn' j).ne', Real.log_mul (hcl0 j).ne' (hcl0' j).ne',
    Real.log_mul hXpos.ne' hPP.ne', hlogX, hlogP, Finset.sum_add_distrib] at hl
  simp only [liftedMapLogSize]
  linarith
end Formalism.DimensionVariation
