-- Prove2me | solution 1 for ClassicalComplexWPT.normalizedScale_sub_monomial_apply_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:06:42.989023+00:00
-- url     : https://prove2.me/submissions/aeebca28-4651-4886-b481-20339047287e

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
import Theorems.Thm_ClassicalComplexWPT_lastSlice_zero
import Theorems.Thm_ClassicalComplexWPT_monomial_zero
import Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
attribute [local simp] ClassicalComplexWPT.lastAxis_apply
attribute [local simp] ClassicalComplexWPT.lastSlice_zero
attribute [local simp] ClassicalComplexWPT.monomial_zero
attribute [local simp] ClassicalComplexWPT.weightedLastCoeffs_apply



set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT
namespace ClassicalComplexWPT
theorem _root_.solution {t : ℝ≥0} (ht : t ≤ 1) (ht0 : 0 < t)
    (f : OriginSeq) (d k : ℕ) (hlow : ∀ j < d, f j = 0) (hfd : f d ≠ 0) :
    ‖(normalizedScale t ht f d - monomialSeq d) k‖ ≤
      ((t : ℝ) / ‖f d‖) * ‖f k‖ := by
  change ‖normalizedScale t ht f d k - monomialSeq d k‖ ≤
    ((t : ℝ) / ‖f d‖) * ‖f k‖
  by_cases hkd : k < d
  · have hne : k ≠ d := ne_of_lt hkd
    simp [normalizedScale_apply, monomialSeq_apply_ne hne, hlow k hkd]
  by_cases hdk : k = d
  · subst k
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
    have hprod : (t : ℂ) ^ d * f d ≠ 0 := mul_ne_zero (pow_ne_zero _ htC) hfd
    have heq : normalizedScale t ht f d d = 1 := by
      rw [normalizedScale_apply, inv_mul_cancel₀ hprod]
    rw [heq, monomialSeq_apply_same, sub_self, norm_zero]
    positivity
  have hdkle : d ≤ k := Nat.le_of_not_gt hkd
  have hdklt : d < k := lt_of_le_of_ne hdkle (Ne.symm hdk)
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht0.ne'
  have htpowd : (t : ℂ) ^ d ≠ 0 := pow_ne_zero _ htC
  rw [normalizedScale_apply, monomialSeq_apply_ne hdk, sub_zero]
  rw [norm_mul, norm_inv, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg t.coe_nonneg]
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg t.coe_nonneg]
  have htRpos : 0 < (t : ℝ) := by exact_mod_cast ht0
  have htRne : (t : ℝ) ≠ 0 := htRpos.ne'
  have hfdnorm : ‖f d‖ ≠ 0 := norm_ne_zero_iff.mpr hfd
  have hpow : (t : ℝ) ^ k = (t : ℝ) ^ (k - d) * (t : ℝ) ^ d := by
    rw [← pow_add, Nat.sub_add_cancel hdkle]
  have heq :
      (((t : ℝ) ^ d * ‖f d‖)⁻¹ * ((t : ℝ) ^ k * ‖f k‖)) =
        (((t : ℝ) ^ (k - d)) / ‖f d‖) * ‖f k‖ := by
    rw [hpow]
    field_simp
  rw [heq]
  gcongr
  apply pow_le_of_le_one t.coe_nonneg (by exact_mod_cast ht)
  omega
end ClassicalComplexWPT
