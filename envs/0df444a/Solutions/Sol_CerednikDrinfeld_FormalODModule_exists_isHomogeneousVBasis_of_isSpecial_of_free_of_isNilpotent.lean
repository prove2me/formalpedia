-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.exists_isHomogeneousVBasis_of_isSpecial_of_free_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/01a21b5f-eaf7-5d19-b548-a325ee051af8

import Mathlib
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCompl_gradedPiece_zero_one_of_isNilpotent
import Theorems.Thm_CerednikDrinfeld_FormalODModule_tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent
import Theorems.Thm_MvFormalGroup_CartierModule_verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free_of_isNilpotent
p2m_attr_erase "instance" "MvFormalGroup.SeriesPoint.instAddCommGroup MvFormalGroup.SeriesPoint.instNeg MvFormalGroup.SeriesPoint.instAdd MvFormalGroup.SeriesPoint.instZero MvFormalGroup.WittLaw.charP_mvPowerSeries MvFormalGroup.SeriesPoint.instAddGroup"
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply MvFormalGroup.BigWittLaw.projPoly_zero MvFormalGroup.BigWittLaw.constantCoeff_frobFactor MvFormalGroup.BigWittLaw.constantCoeff_geomSeries MvFormalGroup.BigWittLaw.wittCoordFam_apply MvFormalGroup.BigWittLaw.wittCoord_zero MvFormalGroup.BigWittLaw.constantCoeff_killProd MvFormalGroup.BigWittLaw.constantCoeff_genSeries MvFormalGroup.BigWittLaw.coeff_genSeries_zero MvFormalGroup.BigWittLaw.frobFam_apply MvFormalGroup.BigWittLaw.coeff_genSeries_succ MvFormalGroup.BigWittLaw.projFam_apply MvFormalGroup.WittLaw.pairSeries_one MvFormalGroup.SeriesPoint.val_neg MvFormalGroup.WittLaw.coe_verPt MvFormalGroup.WittLaw.coeff_curveTautPt MvFormalGroup.WittLaw.coe_wittSMulPt MvFormalGroup.WittLaw.coe_frobPt MvFormalGroup.WittLaw.coeff_tautPt MvFormalGroup.WittLaw.coe_add_coeff MvFormalGroup.SeriesPoint.val_substPt MvFormalGroup.WittLaw.coeff_frobPt MvFormalGroup.WittLaw.pairSeries_zero MvFormalGroup.WittLaw.coeff_teichPt MvFormalGroup.SeriesPoint.val_mapPt MvFormalGroup.CartierModule.val_evalPtFun MvFormalGroup.CartierModule.presPiHom_apply MvFormalGroup.SeriesPoint.val_zero MvFormalGroup.SeriesPoint.val_add MvFormalGroup.CartierModule.val_evalPt MvFormalGroup.WittLaw.coeff_substPt MvFormalGroup.SeriesPoint.mk.injEq MvFormalGroup.SeriesPoint.mk.sizeOf_spec"

set_option autoImplicit false

universe u

open MvFormalGroup MvFormalGroup.CartierModule CerednikDrinfeld

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type u} [CommRing B] [Algebra ℤ_[p] B]
    (j : CerednikDrinfeld.Zp2 p →+* B) (hB : IsNilpotent (p : B)) (X : CerednikDrinfeld.FormalODModule p B)
    (hX : X.IsSpecial j) (h₀ : Module.Free B ↥(X.lieZero j)) (h₁ : Module.Free B ↥(X.lieOne j)) :
    ∃ γ : Fin 2 → MvFormalGroup.CartierModule p X.F, X.IsHomogeneousVBasis j γ := by
  classical
  obtain ⟨hc, hinv₀, hinv₁⟩ := hX
  haveI := hinv₀; haveI := hinv₁; haveI := h₀; haveI := h₁

  have hM := CerednikDrinfeld.FormalODModule.isCompl_gradedPiece_zero_one_of_isNilpotent p j hB X
  have hT := CerednikDrinfeld.FormalODModule.tangent_mem_lieZero_and_lieOne_of_mem_gradedPiece_of_isNilpotent p j hB X
  have hsurj := (MvFormalGroup.CartierModule.verschiebungInt_injective_and_tangent_surjective_and_ker_and_complete_of_algebra_padicInt
    p X.F).2.1

  have lift : ∀ t : X.Lie, ∃ m₀ ∈ X.gradedPiece j 0, ∃ m₁ ∈ X.gradedPiece j 1,
      tangent m₀ + tangent m₁ = t ∧ tangent m₀ ∈ X.lieZero j ∧ tangent m₁ ∈ X.lieOne j := by
    intro t
    obtain ⟨m, rfl⟩ := hsurj t
    have hm : m ∈ X.gradedPiece j 0 ⊔ X.gradedPiece j 1 := by
      rw [hM.codisjoint.eq_top]; trivial
    obtain ⟨m₀, hm₀, m₁, hm₁, rfl⟩ := AddSubgroup.mem_sup.1 hm
    exact ⟨m₀, hm₀, m₁, hm₁, (map_add _ _ _).symm, hT.1 m₀ hm₀, hT.2 m₁ hm₁⟩
  have lift₀ : ∀ t ∈ X.lieZero j, ∃ m ∈ X.gradedPiece j 0, tangent m = t := by
    intro t ht
    obtain ⟨m₀, hm₀, m₁, hm₁, hsum, ht₀, ht₁⟩ := lift t
    have h1 : tangent m₁ ∈ X.lieZero j := by
      have : tangent m₁ = t - tangent m₀ := by rw [← hsum]; abel
      rw [this]; exact Submodule.sub_mem _ ht ht₀
    have h0 : tangent m₁ = 0 := (Submodule.disjoint_def.1 hc.disjoint) _ h1 ht₁
    exact ⟨m₀, hm₀, by rw [← hsum, h0, add_zero]⟩
  have lift₁ : ∀ t ∈ X.lieOne j, ∃ m ∈ X.gradedPiece j 1, tangent m = t := by
    intro t ht
    obtain ⟨m₀, hm₀, m₁, hm₁, hsum, ht₀, ht₁⟩ := lift t
    have h1 : tangent m₀ ∈ X.lieOne j := by
      have : tangent m₀ = t - tangent m₁ := by rw [← hsum]; abel
      rw [this]; exact Submodule.sub_mem _ ht ht₁
    have h0 : tangent m₀ = 0 := (Submodule.disjoint_def.1 hc.disjoint) _ ht₀ h1
    exact ⟨m₁, hm₁, by rw [← hsum, h0, zero_add]⟩

  obtain ⟨e₀⟩ := (Module.Invertible.free_iff_linearEquiv (R := B) (M := ↥(X.lieZero j))).1 h₀
  obtain ⟨e₁⟩ := (Module.Invertible.free_iff_linearEquiv (R := B) (M := ↥(X.lieOne j))).1 h₁
  obtain ⟨γ₀, hγ₀, htγ₀⟩ := lift₀ _ (e₀.symm 1).2
  obtain ⟨γ₁, hγ₁, htγ₁⟩ := lift₁ _ (e₁.symm 1).2
  refine ⟨![γ₀, γ₁], ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hγ₀
    · exact hγ₁
  ·
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.vecMul_surjective_iff_isUnit]
    intro v
    have hv : v ∈ X.lieZero j ⊔ X.lieOne j := by rw [hc.codisjoint.eq_top]; trivial
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    have hy' : y = e₀ ⟨y, hy⟩ • ((e₀.symm 1 : ↥(X.lieZero j)) : X.Lie) := by
      have h : e₀.symm (e₀ ⟨y, hy⟩ • (1 : B)) = ⟨y, hy⟩ := by
        rw [smul_eq_mul, mul_one]; exact e₀.symm_apply_apply _
      rw [map_smul] at h
      exact (congrArg Subtype.val h).symm
    have hz' : z = e₁ ⟨z, hz⟩ • ((e₁.symm 1 : ↥(X.lieOne j)) : X.Lie) := by
      have h : e₁.symm (e₁ ⟨z, hz⟩ • (1 : B)) = ⟨z, hz⟩ := by
        rw [smul_eq_mul, mul_one]; exact e₁.symm_apply_apply _
      rw [map_smul] at h
      exact (congrArg Subtype.val h).symm
    refine ⟨![e₀ ⟨y, hy⟩, e₁ ⟨z, hz⟩], ?_⟩
    funext k
    show (∑ i, ![e₀ ⟨y, hy⟩, e₁ ⟨z, hz⟩] i * (Matrix.of fun i k => tangent (![γ₀, γ₁] i) k) i k) = (y + z) k
    rw [Fin.sum_univ_two]
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.add_apply,
      htγ₀, htγ₁]
    conv_rhs => rw [hy', hz']
    simp only [Pi.smul_apply, smul_eq_mul]

end S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_exists_isHomogeneousVBasis_of_isSpecial_of_free_of_isNilpotent (solution)
