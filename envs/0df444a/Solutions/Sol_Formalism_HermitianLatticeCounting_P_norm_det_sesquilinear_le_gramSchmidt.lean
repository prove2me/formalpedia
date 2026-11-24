-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.norm_det_sesquilinear_le_gramSchmidt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:17:25.764799+00:00
-- url     : https://prove2.me/submissions/548cfec0-e0bf-442c-bf32-126cd4c1a67c

import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LatticeSumBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_SchurAverage
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_gramSchmidt_coeff_eq_one
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_eq_sum_gramSchmidt_coeff
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_det_sesquilinear_change_basis
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_det_le_prod_row_norms
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_norm_sq_orthogonal_sum_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open InnerProductSpace
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hB : ∀ x y, ‖B x y‖ ≤ c * ‖x‖ * ‖y‖) {j : ℕ} (y : Fin j → V₁) (y' : Fin j → V₂) :
    ‖(Matrix.of fun a b => B (y a) (y' b)).det‖ ≤
      c ^ j * (∏ i, ‖gramSchmidt ℂ y i‖) * ∏ k, ‖gramSchmidt ℂ y' k‖ := by
  set g := gramSchmidt ℂ y with hg
  set g' := gramSchmidt ℂ y' with hg'
  have e1 : (Matrix.of fun a b => B (y a) (y' b)).det = (Matrix.of fun i k => B (g i) (g' k)).det := by
    have : (Matrix.of fun a b => B (y a) (y' b)) =
        Matrix.of fun a b => B (∑ i, s5bL y a i • g i) (∑ k, s5bL y' b k • g' k) := by
      ext a b; simp only [Matrix.of_apply, hg, hg', ← eq_sum_gramSchmidt_coeff]
    rw [this, det_sesquilinear_change_basis, det_gramSchmidt_coeff_eq_one, det_gramSchmidt_coeff_eq_one]; simp
  set gh : Fin j → V₂ := fun k => ((‖g' k‖⁻¹ : ℝ) : ℂ) • g' k with hgh
  have e2 : ∀ i k, B (g i) (g' k) = (‖g' k‖ : ℂ) * B (g i) (gh k) := by
    intro i k
    simp only [hgh, LinearMap.map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul]
    by_cases h0 : ‖g' k‖ = 0
    · have : g' k = 0 := norm_eq_zero.mp h0
      simp [this]
    · rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h0]; simp
  set Nt : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun i k => B (g i) (gh k) with hNt
  have e3 : (Matrix.of fun i k => B (g i) (g' k)).det = (∏ k, (‖g' k‖ : ℂ)) * Nt.det := by
    rw [← Matrix.det_mul_row]; congr 1; ext i k; simp only [Matrix.of_apply, hNt]; exact e2 i k
  have hgh_orth : ∀ k l, k ≠ l → inner ℂ (gh k) (gh l) = 0 := by
    intro k l hkl
    simp only [hgh, inner_smul_left, inner_smul_right, hg', gramSchmidt_orthogonal ℂ y' hkl, mul_zero]
  have hgh1 : ∀ k, ‖gh k‖ ≤ 1 := by
    intro k
    simp only [hgh, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    by_cases h0 : ‖g' k‖ = 0
    · simp [h0]
    · rw [inv_mul_cancel₀ h0]
  have hrow : ∀ i, Real.sqrt (∑ k, ‖Nt i k‖ ^ 2) ≤ c * ‖g i‖ := by
    intro i
    set T := ∑ k, ‖Nt i k‖ ^ 2 with hT
    have hT0 : 0 ≤ T := Finset.sum_nonneg fun k _ => by positivity
    set w := ∑ k, Nt i k • gh k with hw
    have hBw : B (g i) w = (T : ℂ) := by
      simp only [hw, map_sum, LinearMap.map_smulₛₗ, smul_eq_mul, hT]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      have : B (g i) (gh k) = Nt i k := rfl
      rw [this, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have hwn : ‖w‖ ≤ Real.sqrt T :=
      Real.le_sqrt_of_sq_le (norm_sq_orthogonal_sum_le gh hgh_orth hgh1 (fun k => Nt i k))
    have h1 := hB (g i) w
    rw [hBw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0] at h1
    have h2 : T ≤ c * ‖g i‖ * Real.sqrt T :=
      h1.trans (mul_le_mul_of_nonneg_left hwn (by positivity))
    rcases hT0.lt_or_eq with hp | hz
    · have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hp
      have hss : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0
      nlinarith
    · rw [← hz, Real.sqrt_zero]; positivity
  rw [e1, e3, norm_mul, norm_prod]
  simp only [Complex.norm_real, norm_norm]
  calc (∏ k, ‖g' k‖) * ‖Nt.det‖ ≤ (∏ k, ‖g' k‖) * ∏ i, (c * ‖g i‖) := by
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        exact (norm_det_le_prod_row_norms Nt).trans
          (Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _) fun i _ => hrow i)
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]; ring
end Formalism.HermitianLatticeCounting.P
