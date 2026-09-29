-- Prove2me | solution 1 for CuspForm.exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6499b9d4-29f1-5dc1-9fd8-8bc1250c3781

import Mathlib
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj

set_option autoImplicit false

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm ComplexConjugate

namespace ConjFormGamma1

def conjNeg (γ : SL(2, ℤ)) : SL(2, ℤ) :=
  ⟨!![γ 0 0, -γ 0 1; -γ 1 0, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    have := Matrix.det_fin_two γ.1
    rw [γ.2] at this
    linear_combination (-1 : ℤ) * this⟩

@[scoped simp] theorem conjNeg_apply_00 (γ : SL(2, ℤ)) : (conjNeg γ) 0 0 = γ 0 0 := rfl
@[scoped simp] theorem conjNeg_apply_01 (γ : SL(2, ℤ)) : (conjNeg γ) 0 1 = -γ 0 1 := rfl
@[scoped simp] theorem conjNeg_apply_10 (γ : SL(2, ℤ)) : (conjNeg γ) 1 0 = -γ 1 0 := rfl
@[scoped simp] theorem conjNeg_apply_11 (γ : SL(2, ℤ)) : (conjNeg γ) 1 1 = γ 1 1 := rfl

theorem conjNeg_conjNeg (γ : SL(2, ℤ)) : conjNeg (conjNeg γ) = γ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem conjNeg_mem_Gamma1_iff (M : ℕ) (γ : SL(2, ℤ)) :
    conjNeg γ ∈ Gamma1 M ↔ γ ∈ Gamma1 M := by
  simp only [Gamma1_mem, conjNeg_apply_00, conjNeg_apply_11, conjNeg_apply_10, Int.cast_neg,
    neg_eq_zero]

theorem J_mul_coe_mul_J (γ : SL(2, ℤ)) :
    J * (γ : GL (Fin 2) ℝ) * J = ((conjNeg γ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [J, Matrix.mul_apply, Fin.sum_univ_two, conjNeg, Matrix.vecMul, dotProduct,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

open ConjAct Pointwise

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem J_inv : (J : GL (Fin 2) ℝ)⁻¹ = J := by
  rw [inv_eq_iff_mul_eq_one, ← sq, J_sq]

theorem mem_map_Gamma1_iff (M : ℕ) (x : GL (Fin 2) ℝ) :
    x ∈ (Γ₁ℝ M) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 M ∧ (γ : GL (Fin 2) ℝ) = x :=
  Subgroup.mem_map

theorem J_mul_mul_J_mem (M : ℕ) {x : GL (Fin 2) ℝ} (hx : x ∈ (Γ₁ℝ M)) : J * x * J ∈ (Γ₁ℝ M) := by
  obtain ⟨γ, hγ, rfl⟩ := (mem_map_Gamma1_iff M x).1 hx
  rw [J_mul_coe_mul_J]
  exact (mem_map_Gamma1_iff M _).2 ⟨conjNeg γ, (conjNeg_mem_Gamma1_iff M γ).2 hγ, rfl⟩

theorem toConjAct_J_inv_smul (M : ℕ) : toConjAct (J : GL (Fin 2) ℝ)⁻¹ • (Γ₁ℝ M) = (Γ₁ℝ M) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul,
    J_inv]
  constructor
  · intro h
    have := J_mul_mul_J_mem M h
    rwa [← mul_assoc, ← mul_assoc, ← sq, J_sq, one_mul, mul_assoc, ← sq, J_sq, mul_one] at this
  · exact J_mul_mul_J_mem M

theorem slash_J_apply (f : ℍ → ℂ) (k : ℤ) (τ : ℍ) :
    (f ∣[k] J) τ = conj (f (ofComplex (-conj (τ : ℂ)))) := by
  simp [ModularForm.slash_def, J_smul]

noncomputable def conjForm {M : ℕ} {k : ℤ} (g : CuspForm (Γ₁ℝ M) k) : CuspForm (Γ₁ℝ M) k :=
  (CuspForm.translate g J).copy (fun τ => conj (g (ofComplex (-conj (τ : ℂ)))))
    (by funext τ; rw [CuspForm.translate]; exact (slash_J_apply g k τ).symm)
    (toConjAct_J_inv_smul M).symm

theorem conjForm_apply {M : ℕ} {k : ℤ} (g : CuspForm (Γ₁ℝ M) k) (τ : ℍ) :
    conjForm g τ = conj (g (ofComplex (-conj (τ : ℂ)))) := rfl

theorem one_mem_strictPeriods (M : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ M).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem conj_qParam_J_smul (τ : ℍ) :
    conj (Function.Periodic.qParam 1 (↑(J • τ) : ℂ)) = Function.Periodic.qParam 1 (τ : ℂ) := by
  rw [Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_conj, coe_J_smul]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, map_neg,
    Complex.conj_conj, Complex.ofReal_one, div_one]
  ring

theorem qCoeff_conjForm {M : ℕ} {k : ℤ} (g : CuspForm (Γ₁ℝ M) k) (n : ℕ) :
    ModularFormClass.qCoeff (conjForm g) n = conj (ModularFormClass.qCoeff g n) := by
  have hbdd : IsBoundedAtImInfty (g : ℍ → ℂ) := by
    haveI : Fact (IsCusp OnePoint.infty (Γ₁ℝ M)) :=
      ⟨(Γ₁ℝ M).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods M)⟩
    exact ModularFormClass.bdd_at_infty g
  have hsum : ∀ τ : ℍ, HasSum (fun m : ℕ => conj ((qExpansion 1 g).coeff m) •
      Function.Periodic.qParam 1 (τ : ℂ) ^ m) (conjForm g τ) := by
    intro τ
    have h := UpperHalfPlane.hasSum_qExpansion one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex g (one_mem_strictPeriods M))
      (CuspForm.holo' g) hbdd (J • τ)
    have h' := h.map (starRingEnd ℂ) Complex.continuous_conj
    rw [conjForm_apply, ← J_smul]
    convert h' using 1
    funext m
    simp only [Function.comp_apply, smul_eq_mul, map_mul, map_pow, conj_qParam_J_smul]
  symm
  exact ModularFormClass.qExpansion_coeff_unique one_pos (one_mem_strictPeriods M)
    (f := conjForm g) hsum n

end ConjFormGamma1
p2m_reactivate "P2MW.S_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj.ConjFormGamma1"

open scoped MatrixGroups in
theorem solution
    (M : ℕ) (k : ℤ) (g : CuspForm (Gamma1 M) k) :
    ∃ g' : CuspForm (Gamma1 M) k,
      (∀ τ τ' : UpperHalfPlane, (τ' : ℂ) = -(starRingEnd ℂ (τ : ℂ)) →
        g' τ = starRingEnd ℂ (g τ')) ∧
      ∀ n : ℕ, ModularFormClass.qCoeff g' n = starRingEnd ℂ (ModularFormClass.qCoeff g n) := by
  refine ⟨ConjFormGamma1.conjForm g, fun τ τ' h => ?_, ConjFormGamma1.qCoeff_conjForm g⟩
  rw [ConjFormGamma1.conjForm_apply]
  congr 2
  apply UpperHalfPlane.ext
  rw [h, UpperHalfPlane.ofComplex_apply_of_im_pos]
  simpa using τ.im_pos

end S_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj
end P2MW
export P2MW.S_CuspForm_exists_gamma1_apply_eq_conj_and_qCoeff_eq_conj (solution)
