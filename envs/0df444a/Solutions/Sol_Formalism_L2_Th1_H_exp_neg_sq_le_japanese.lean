-- Prove2me | solution 1 for Formalism.L2.Th1.H.exp_neg_sq_le_japanese
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T10:26:12.626489+00:00
-- url     : https://prove2.me/submissions/cf60ac7f-f3e7-440b-8485-69de0017b4dd

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_GaloisDescentSubspaces
import Theorems.Thm_Formalism_L2_Th1_H_exp_neg_le_factorial_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate Nat
open MeasureTheory
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
namespace Formalism.L2.Th1.H
theorem _root_.solution {a : ℝ} (ha : 0 < a) (m : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-a * t ^ 2) ≤ Real.exp a * (m ! : ℝ) * 2 ^ m / a ^ m * (1 + t) ^ (-((2 * m : ℕ) : ℝ)) := by
  have hs : 0 < a * (1 + t ^ 2) := by positivity
  have h1 := exp_neg_le_factorial_div hs m
  have h2 : (1 + t) ^ 2 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (1 - t)]
  have h3 : (1 + t) ^ (2 * m) ≤ 2 ^ m * (1 + t ^ 2) ^ m := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 m
  have h4 : 0 < (1 + t) ^ (2 * m) := by positivity
  have h5 : 0 < (1 + t ^ 2) ^ m := by positivity
  have ham : 0 < a ^ m := pow_pos ha m
  have hf : (0 : ℝ) < (m ! : ℝ) := by exact_mod_cast m.factorial_pos
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have e : -a * t ^ 2 = a + -(a * (1 + t ^ 2)) := by ring
  rw [e, Real.exp_add]
  have h6 : ((1 + t ^ 2) ^ m)⁻¹ ≤ 2 ^ m * ((1 + t) ^ (2 * m))⁻¹ := by
    rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ h5 h4]
    linarith
  calc Real.exp a * Real.exp (-(a * (1 + t ^ 2)))
      ≤ Real.exp a * ((m ! : ℝ) / (a * (1 + t ^ 2)) ^ m) :=
        mul_le_mul_of_nonneg_left h1 (Real.exp_pos a).le
    _ = Real.exp a * (m ! : ℝ) / a ^ m * ((1 + t ^ 2) ^ m)⁻¹ := by
        rw [mul_pow]; field_simp
    _ ≤ Real.exp a * (m ! : ℝ) / a ^ m * (2 ^ m * ((1 + t) ^ (2 * m))⁻¹) :=
        mul_le_mul_of_nonneg_left h6 (by positivity)
    _ = Real.exp a * (m ! : ℝ) * 2 ^ m / a ^ m * ((1 + t) ^ (2 * m))⁻¹ := by ring
end Formalism.L2.Th1.H
