-- Prove2me | solution 1 for CongruenceSubgroup.conj_T_zpow_mem_Gamma1_of_mem_sup_zpowers_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/3761268e-163f-5b0c-8713-5137caf71e30

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CongruenceSubgroup_conj_T_zpow_mem_Gamma1_of_mem_sup_zpowers_neg_one

set_option autoImplicit false

open scoped MatrixGroups

namespace RegCuspAux

def pmGamma1 (M : ℕ) : Subgroup SL(2, ℤ) where
  carrier := {g | g ∈ CongruenceSubgroup.Gamma1 M ∨ -g ∈ CongruenceSubgroup.Gamma1 M}
  one_mem' := Or.inl (one_mem _)
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (mul_mem ha hb)
    · exact Or.inr (by rw [← mul_neg]; exact mul_mem ha hb)
    · exact Or.inr (by rw [← neg_mul]; exact mul_mem ha hb)
    · exact Or.inl (by rw [← neg_mul_neg]; exact mul_mem ha hb)
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (inv_mem ha)
    · refine Or.inr ?_
      have h : (-a)⁻¹ = -a⁻¹ := inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
      rw [← h]; exact inv_mem ha

theorem mem_pmGamma1_iff (M : ℕ) (g : SL(2, ℤ)) :
    g ∈ pmGamma1 M ↔ g ∈ CongruenceSubgroup.Gamma1 M ∨ -g ∈ CongruenceSubgroup.Gamma1 M := Iff.rfl

theorem sup_le_pmGamma1 (M : ℕ) :
    CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ)) ≤ pmGamma1 M :=
  sup_le (fun _ hg => Or.inl hg)
    (Subgroup.zpowers_le.2 (Or.inr (by rw [neg_neg]; exact one_mem _)))

theorem trace_conj_T_zpow (σ : SL(2, ℤ)) (h : ℤ) :
    ((σ * ModularGroup.T ^ h * σ⁻¹ : SL(2, ℤ)) 0 0 : ℤ) + (σ * ModularGroup.T ^ h * σ⁻¹ : SL(2, ℤ)) 1 1 = 2 := by
  have h1 : Matrix.trace ((σ * ModularGroup.T ^ h * σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      Matrix.trace ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_assoc,
      Matrix.trace_mul_comm, Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two] at h1
  have h2 : ((ModularGroup.T ^ h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, h; 0, 1] :=
    ModularGroup.coe_T_zpow h
  rw [h2] at h1
  simpa using h1

end RegCuspAux

theorem solution (M : ℕ) (hM : ¬ M ∣ 4)
    (σ : SL(2, ℤ)) (h : ℤ) (hmem : σ * ModularGroup.T ^ h * σ⁻¹ ∈ CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))) :
    σ * ModularGroup.T ^ h * σ⁻¹ ∈ CongruenceSubgroup.Gamma1 M := by
  rcases (RegCuspAux.sup_le_pmGamma1 M hmem) with hg | hg
  · exact hg
  · exfalso
    apply hM
    set g : SL(2, ℤ) := σ * ModularGroup.T ^ h * σ⁻¹ with hgdef
    have htr : (g 0 0 : ℤ) + g 1 1 = 2 := RegCuspAux.trace_conj_T_zpow σ h
    have hneg := (CongruenceSubgroup.Gamma1_mem M (-g)).1 hg
    have e00 : ((-g : SL(2, ℤ)) 0 0 : ℤ) = -(g 0 0) := by
      simp [Matrix.SpecialLinearGroup.coe_neg]
    have e11 : ((-g : SL(2, ℤ)) 1 1 : ℤ) = -(g 1 1) := by
      simp [Matrix.SpecialLinearGroup.coe_neg]
    have h00 : (((-(g 0 0) : ℤ)) : ZMod M) = 1 := by rw [← e00]; exact hneg.1
    have h11 : (((-(g 1 1) : ℤ)) : ZMod M) = 1 := by rw [← e11]; exact hneg.2.1
    have h2 : (((-2 : ℤ)) : ZMod M) = ((2 : ℤ) : ZMod M) := by
      have : (((-(g 0 0 + g 1 1) : ℤ)) : ZMod M) = 2 := by
        push_cast at h00 h11 ⊢
        linear_combination h00 + h11
      rw [htr] at this
      exact_mod_cast this
    have h3 := ((ZMod.intCast_eq_intCast_iff (-2) 2 M).1 h2).dvd
    norm_num at h3
    exact_mod_cast h3

#print axioms solution

end S_CongruenceSubgroup_conj_T_zpow_mem_Gamma1_of_mem_sup_zpowers_neg_one
end P2MW
export P2MW.S_CongruenceSubgroup_conj_T_zpow_mem_Gamma1_of_mem_sup_zpowers_neg_one (solution)
