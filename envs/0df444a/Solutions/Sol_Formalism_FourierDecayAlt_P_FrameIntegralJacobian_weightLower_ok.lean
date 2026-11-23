-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.FrameIntegralJacobian.weightLower_ok
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:03:10.141963+00:00
-- url     : https://prove2.me/submissions/3c33b9dc-74d9-4b3f-a314-5ddc47eea779

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FrameIntegralJacobian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
open scoped ComplexOrder
noncomputable section
namespace Formalism.FourierDecayAlt.P.FrameIntegralJacobian
open Formalism.FourierDecayAlt.PairingProductCorollary
private lemma bern_lemma (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) (n : ℕ) :
    1 - (n : ℝ) * x ≤ (1 - x) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hx : 0 ≤ 1 - x := by linarith
    have hm := mul_le_mul_of_nonneg_right ih hx
    rw [pow_succ]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (mul_nonneg h0 h0)]
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
end
end

set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.FrameIntegralJacobian
open Formalism.FourierDecayAlt.PairingProductCorollary
namespace Formalism.FourierDecayAlt.P.FrameIntegralJacobian
theorem _root_.solution : WeightLower := by
  unfold WeightLower
  intro N m f hN hm hf
  have hN4 : (4:ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (N:ℝ) ≠ 0 := by positivity
  have hxN2 : 1 / (N:ℝ) ^ 2 * (N:ℝ) ^ 2 = 1 := by field_simp
  have hx0 : 0 ≤ 1 / (N:ℝ) ^ 2 := by positivity
  have hNx : (N:ℝ) * (1 / (N:ℝ) ^ 2) ≤ 1 / 4 := by
    nlinarith [mul_nonneg (mul_nonneg hx0 (by linarith : (0:ℝ) ≤ N)) (by linarith : (0:ℝ) ≤ (N:ℝ) - 4)]
  have hx1 : 1 / (N:ℝ) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg hx0 (by linarith : (0:ℝ) ≤ (N:ℝ) - 4)]
  have ht0 : 0 ≤ 1 - 1 / (N:ℝ) ^ 2 := by linarith
  have ht1 : 1 - 1 / (N:ℝ) ^ 2 ≤ 1 := by linarith
  have hprod : ∏ _i : Fin m, (1 - 1 / (N:ℝ) ^ 2) ≤ ∏ i, f i :=
    Finset.prod_le_prod (fun i _ => ht0) (fun i _ => hf i)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hprod
  have hpow : (1 - 1 / (N:ℝ) ^ 2) ^ N ≤ (1 - 1 / (N:ℝ) ^ 2) ^ m :=
    pow_le_pow_of_le_one ht0 ht1 hm
  have hbern := bern_lemma (1 / (N:ℝ) ^ 2) hx0 hx1 N
  have hexp : Real.exp (-(1 / 2)) ≤ 3 / 4 := by
    have e1 := Real.add_one_le_exp (1 / 2 : ℝ)
    have e2 : Real.exp (-(1 / 2)) * Real.exp (1 / 2) = 1 := by
      rw [← Real.exp_add]; simp
    have e3 := Real.exp_pos (-(1 / 2))
    nlinarith
  linarith
end Formalism.FourierDecayAlt.P.FrameIntegralJacobian
