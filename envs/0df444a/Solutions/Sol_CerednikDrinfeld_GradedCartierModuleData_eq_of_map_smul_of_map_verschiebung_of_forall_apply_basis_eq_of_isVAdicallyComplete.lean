-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e1b70fc3-00df-507f-a3d7-93f70fa47071

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Definitions.Def_CerednikDrinfeld_DrinfeldQuadruple
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_CartierQuadruple
import Definitions.Def_CerednikDrinfeld_PeriodMapSpec
import Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

theorem solution
    (p : ℕ) [Fact p.Prime] {R B' : Type} [CommRing R] [CommRing B']
    {jR : CerednikDrinfeld.Zp2 p →+* R} {j' : CerednikDrinfeld.Zp2 p →+* B'} (φ : R →+* B')
    (D : CerednikDrinfeld.GradedCartierModuleData p R jR)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' j') (hD' : D'.IsVAdicallyComplete)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ)
    (δ₁ δ₂ : D.M →+ D'.M)
    (h₁ : ∀ (w : WittVector p R) (x : D.M), δ₁ (w • x) = WittVector.map φ w • δ₁ x)
    (h₁V : ∀ x : D.M, δ₁ (D.verschiebung x) = D'.verschiebung (δ₁ x))
    (h₂ : ∀ (w : WittVector p R) (x : D.M), δ₂ (w • x) = WittVector.map φ w • δ₂ x)
    (h₂V : ∀ x : D.M, δ₂ (D.verschiebung x) = D'.verschiebung (δ₂ x))
    (hγeq : ∀ i : Fin 2, δ₁ (γ i) = δ₂ (γ i)) :
    δ₁ = δ₂ := by
  have hsub_smul : ∀ (w : WittVector p R) (x : D.M),
      (δ₁ - δ₂) (w • x) = WittVector.map φ w • (δ₁ - δ₂) x := by
    intro w x; simp only [AddMonoidHom.sub_apply, h₁, h₂, smul_sub]
  have hsubV : ∀ x, (δ₁ - δ₂) (D.verschiebung x) = D'.verschiebung ((δ₁ - δ₂) x) := by
    intro x; simp only [AddMonoidHom.sub_apply, h₁V, h₂V, map_sub]
  have hsubγ : ∀ i, (δ₁ - δ₂) (γ i) = 0 := by
    intro i; simp only [AddMonoidHom.sub_apply, hγeq, sub_self]
  have key : ∀ N : ℕ, ∀ x : D.M, ∃ t : D'.M, (δ₁ - δ₂) x = (⇑D'.verschiebung)^[N] t := by
    intro N
    induction N with
    | zero => intro x; exact ⟨_, rfl⟩
    | succ N ih =>
      intro x
      obtain ⟨cy, hcy, -⟩ := hγ.2 x
      obtain ⟨t, ht⟩ := ih cy.2
      refine ⟨t, ?_⟩
      have hz : ∀ i, (δ₁ - δ₂) (WittVector.teichmuller p (cy.1 i) • γ i) = 0 := fun i => by
        rw [hsub_smul, hsubγ, smul_zero]
      rw [hcy, map_add, map_sum, hsubV, ht, Function.iterate_succ_apply']
      simp only [hz, Finset.sum_const_zero, zero_add]
  have hzero : ∀ x, (δ₁ - δ₂) x = 0 := by
    intro x
    refine (hD' (fun _ => 0)).unique ?_ ?_
    · intro N
      obtain ⟨t, ht⟩ := key N x
      exact ⟨t, by simp only [iterate_map_zero, Finset.sum_const_zero, zero_add]; exact ht⟩
    · intro N
      exact ⟨0, by simp only [iterate_map_zero, Finset.sum_const_zero, zero_add]⟩
  ext x
  have := hzero x
  rwa [AddMonoidHom.sub_apply, sub_eq_zero] at this

end S_CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_eq_of_map_smul_of_map_verschiebung_of_forall_apply_basis_eq_of_isVAdicallyComplete (solution)
