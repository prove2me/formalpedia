-- Prove2me | solution 1 for CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/04e3407d-5b98-5374-ba0a-cd235750680c

import Mathlib
import Definitions.Def_ModularCurve_PeriodHomPair
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem

set_option autoImplicit false

open UpperHalfPlane Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm ComplexConjugate Pointwise

noncomputable section

namespace CuspForm
p2m_export "CuspForm" "translate ext"
namespace ConjInvolution
p2m_open "CuspForm"

theorem J_inv_mul_mapGL_mul_J (γ : SL(2, ℤ)) :
    UpperHalfPlane.J⁻¹ * (mapGL ℝ γ : GL (Fin 2) ℝ) * UpperHalfPlane.J =
      (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) := by
  have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two, ModularCurve.Period.jConjMat,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.vecMul, dotProduct]

theorem conjAct_J_inv_smul_eq (Γ : Subgroup SL(2, ℤ))
    (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) :
    ConjAct.toConjAct (UpperHalfPlane.J)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) =
      (Γ : Subgroup (GL (Fin 2) ℝ)) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  constructor
  · rintro ⟨γ, hγ, hx⟩
    refine ⟨ModularCurve.Period.jConjSL γ, hΓ γ hγ, ?_⟩
    rw [← J_inv_mul_mapGL_mul_J]
    rw [show (mapGL ℝ γ : GL (Fin 2) ℝ) = UpperHalfPlane.J * x * UpperHalfPlane.J⁻¹ from hx]
    group
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨ModularCurve.Period.jConjSL γ, hΓ γ hγ, ?_⟩
    change (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) = _
    rw [← J_inv_mul_mapGL_mul_J]
    have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
      rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
    rw [hJ]

def conjOf (Γ : Subgroup SL(2, ℤ)) (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) {k : ℤ}
    (f : CuspForm Γ k) : CuspForm Γ k :=
  (CuspForm.translate f UpperHalfPlane.J).copy ((⇑f) ∣[k] UpperHalfPlane.J) rfl
    (conjAct_J_inv_smul_eq Γ hΓ).symm

theorem conjOf_apply (Γ : Subgroup SL(2, ℤ)) (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) {k : ℤ}
    (f : CuspForm Γ k) (τ : ℍ) : conjOf Γ hΓ f τ = conj (f (UpperHalfPlane.J • τ)) := by
  show ((⇑f) ∣[k] UpperHalfPlane.J) τ = _
  rw [ModularForm.slash_def]
  simp [UpperHalfPlane.sigma_J, UpperHalfPlane.denom_J, UpperHalfPlane.det_J]

end CuspForm.ConjInvolution

end

theorem solution
    (Γ : Subgroup SL(2, ℤ)) (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) (k : ℤ)
    (f : CuspForm Γ k) :
    ∃ g : CuspForm Γ k, ∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ)) :=
  ⟨CuspForm.ConjInvolution.conjOf Γ hΓ f, CuspForm.ConjInvolution.conjOf_apply Γ hΓ f⟩

end S_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
end P2MW
export P2MW.S_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem (solution)
