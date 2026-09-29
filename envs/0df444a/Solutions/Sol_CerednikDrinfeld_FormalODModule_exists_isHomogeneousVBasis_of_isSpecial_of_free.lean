-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_of_free
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/e504afc1-646e-5ac4-a57a-b7f342cb522f

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

universe u

namespace P2mKcVBasis

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld CerednikDrinfeld.FormalODModule

variable {B : Type u} [CommRing B]

theorem exists_generator (L : Submodule B (Fin 2 → B)) [Module.Invertible B L] [Module.Free B L] :
    ∃ (t : L) (e : L →ₗ[B] B), ∀ x : L, x = e x • t := by
  obtain ⟨e⟩ := (Module.Invertible.free_iff_linearEquiv (R := B) (M := L)).mp ‹_›
  refine ⟨e.symm 1, e.toLinearMap, fun x => e.injective ?_⟩
  rw [LinearEquiv.coe_toLinearMap, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]

theorem main (p : ℕ) [Fact p.Prime] [CharP B p]
    (j : Zp2 p →+* B) (X : FormalODModule p B)
    (hX : X.IsSpecial j) (h₀ : Module.Free B ↥(X.lieZero j)) (h₁ : Module.Free B ↥(X.lieOne j)) :
    ∃ γ : Fin 2 → CartierModule p X.F, X.IsHomogeneousVBasis j γ := by
  classical
  obtain ⟨hcompl, hinv₀, hinv₁⟩ := hX
  obtain ⟨t₀, e₀, ht₀⟩ := exists_generator (X.lieZero j)
  obtain ⟨t₁, e₁, ht₁⟩ := exists_generator (X.lieOne j)
  have G := isCompl_gradedPiece_zero_one_of_isCompl_lieZero_lieOne p j X hcompl

  have hm₀ : (t₀ : Fin 2 → B) ∈ (X.gradedPiece j 0).map tangent := by
    rw [G.2.2.2.2.2.2.1]; exact t₀.2
  have hm₁ : (t₁ : Fin 2 → B) ∈ (X.gradedPiece j 1).map tangent := by
    rw [G.2.2.2.2.2.2.2]; exact t₁.2
  obtain ⟨γ₀, hγ₀, htan₀⟩ := AddSubgroup.mem_map.mp hm₀
  obtain ⟨γ₁, hγ₁, htan₁⟩ := AddSubgroup.mem_map.mp hm₁
  refine ⟨![γ₀, γ₁], ?_, ?_⟩
  · intro l
    fin_cases l
    · exact hγ₀
    · exact hγ₁
  ·
    set T : Matrix (Fin 2) (Fin 2) B := Matrix.of fun i k => tangent (![γ₀, γ₁] i) k with hT
    have hrow : ∀ v : Fin 2 → B, Matrix.vecMul v T = v 0 • (t₀ : Fin 2 → B) + v 1 • (t₁ : Fin 2 → B) := by
      intro v
      funext k
      rw [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
      simp only [hT, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [htan₀, htan₁]
    have hsurj : Function.Surjective fun v => Matrix.vecMul v T := by
      intro w
      have hw : w ∈ X.lieZero j ⊔ X.lieOne j := by rw [hcompl.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
      refine ⟨![e₀ ⟨x, hx⟩, e₁ ⟨y, hy⟩], ?_⟩
      show Matrix.vecMul _ T = x + y
      rw [hrow]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      have hx' := congrArg Subtype.val (ht₀ ⟨x, hx⟩)
      have hy' := congrArg Subtype.val (ht₁ ⟨y, hy⟩)
      simp only [Submodule.coe_smul] at hx' hy'
      rw [← hx', ← hy']
    have hunit : IsUnit T := Matrix.vecMul_surjective_iff_isUnit.mp hsurj
    exact (Matrix.isUnit_iff_isUnit_det T).mp hunit

end P2mKcVBasis

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [CharP B p]
    (j : CerednikDrinfeld.Zp2 p →+* B) (X : CerednikDrinfeld.FormalODModule p B)
    (hX : X.IsSpecial j) (h₀ : Module.Free B ↥(X.lieZero j)) (h₁ : Module.Free B ↥(X.lieOne j)) :
    ∃ γ : Fin 2 → MvFormalGroup.CartierModule p X.F, X.IsHomogeneousVBasis j γ :=
  P2mKcVBasis.main p j X hX h₀ h₁

end S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free (solution)
