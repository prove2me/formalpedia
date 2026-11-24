-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts.Bd.inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:56:05.178809+00:00
-- url     : https://prove2.me/submissions/6ab74d96-2f06-4763-91ef-57cf02516ac7

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WirtingerIntegrationByParts
import Theorems.Thm_Formalism_FourierDecayAlt_P_WirtingerIntegrationByParts_gen_norm_iter_inv_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
open Formalism.FourierDecayAlt.G MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
namespace Bd
theorem _root_.solution {f : E → ℝ} {s : Set E} {x : E} {n : ℕ} {κ P : ℝ}
    (hs : IsOpen s) (hx : x ∈ s) (hP : 0 ≤ P) (hf : ContDiffOn ℝ n f s) (hne : ∀ y ∈ s, f y ≠ 0)
    (h0 : 0 < f x) (hκ : 1 ≤ κ) (bf : Bd f s x n (κ * f x) P) :
    Bd (fun y => (f y)⁻¹) s x n ((n.factorial : ℝ) ^ 2 * κ ^ n / f x) P := by
  intro j hj
  have hjn : (j : WithTop ℕ∞) ≤ n := by exact_mod_cast hj
  have hκ0 : 0 ≤ κ := zero_le_one.trans hκ
  set N0 : ℝ := f x with hN0
  have hft : ContDiffOn ℝ n (N0⁻¹ • f) s := hf.const_smul N0⁻¹
  have hmaps : Set.MapsTo (N0⁻¹ • f) s ({0}ᶜ : Set ℝ) := by
    intro y hy
    simp only [Pi.smul_apply, smul_eq_mul, Set.mem_compl_iff, Set.mem_singleton_iff]
    exact mul_ne_zero (inv_ne_zero h0.ne') (hne y hy)
  have hone : (N0⁻¹ • f) x = 1 := by
    simp only [Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ h0.ne'
  have hC : ∀ i, i ≤ j → ‖iteratedFDerivWithin ℝ i (Inv.inv : ℝ → ℝ) {0}ᶜ ((N0⁻¹ • f) x)‖ ≤ (j.factorial : ℝ) := by
    intro i hi
    rw [hone, gen_norm_iter_inv_one]
    exact_mod_cast Nat.factorial_le hi
  have hD : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDerivWithin ℝ i (N0⁻¹ • f) s x‖ ≤ (κ * P) ^ i := by
    intro i hi1 hi
    rw [iteratedFDerivWithin_const_smul_apply
      ((hf.of_le (by exact_mod_cast hi.trans hj)).contDiffWithinAt hx) hs.uniqueDiffOn hx, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h0)]
    have e1 := bf i (hi.trans hj)
    have e2 : N0⁻¹ * ‖iteratedFDerivWithin ℝ i f s x‖ ≤ N0⁻¹ * (κ * N0 * P ^ i) :=
      mul_le_mul_of_nonneg_left e1 (inv_pos.mpr h0).le
    have e3 : N0⁻¹ * (κ * N0 * P ^ i) = κ * P ^ i := by field_simp
    have e4 : κ ≤ κ ^ i := le_self_pow₀ hκ (by omega)
    rw [mul_pow]
    exact (e2.trans e3.le).trans (mul_le_mul_of_nonneg_right e4 (pow_nonneg hP _))
  have hcomp := norm_iteratedFDerivWithin_comp_le (contDiffOn_inv ℝ (n := n)) hft hjn
    isOpen_compl_singleton.uniqueDiffOn hs.uniqueDiffOn hmaps hx hC hD
  have hcd : ContDiffOn ℝ n ((Inv.inv : ℝ → ℝ) ∘ (N0⁻¹ • f)) s := (contDiffOn_inv ℝ (n := n)).comp hft hmaps
  have e0 : (fun y => (f y)⁻¹) = N0⁻¹ • ((Inv.inv : ℝ → ℝ) ∘ (N0⁻¹ • f)) := by
    funext y
    simp only [Pi.smul_apply, Function.comp_apply, smul_eq_mul, mul_inv, inv_inv]
    rw [← mul_assoc, inv_mul_cancel₀ h0.ne', one_mul]
  rw [e0, iteratedFDerivWithin_const_smul_apply ((hcd.of_le hjn).contDiffWithinAt hx) hs.uniqueDiffOn hx,
    norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h0)]
  have f1 : (j.factorial : ℝ) ≤ n.factorial := by exact_mod_cast Nat.factorial_le hj
  have f2 : κ ^ j ≤ κ ^ n := pow_le_pow_right₀ hκ hj
  have f3 : (j.factorial : ℝ) * j.factorial * (κ * P) ^ j ≤ (n.factorial : ℝ) ^ 2 * κ ^ n * P ^ j := by
    rw [mul_pow, sq, ← mul_assoc]
    have g1 : (j.factorial : ℝ) * j.factorial ≤ (n.factorial : ℝ) * n.factorial :=
      mul_le_mul f1 f1 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul g1 f2 (pow_nonneg hκ0 _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
      (pow_nonneg hP _)
  calc N0⁻¹ * ‖iteratedFDerivWithin ℝ j ((Inv.inv : ℝ → ℝ) ∘ (N0⁻¹ • f)) s x‖
      ≤ N0⁻¹ * ((n.factorial : ℝ) ^ 2 * κ ^ n * P ^ j) :=
        mul_le_mul_of_nonneg_left (hcomp.trans f3) (inv_pos.mpr h0).le
    _ = (n.factorial : ℝ) ^ 2 * κ ^ n / N0 * P ^ j := by field_simp
end Bd
end Formalism.FourierDecayAlt.P.WirtingerIntegrationByParts
