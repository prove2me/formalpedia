-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/0da29614-88fa-5504-9f19-4e4a4c9f4082

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierGradedPiece
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_CerednikDrinfeld_CartierModuleModel
import Definitions.Def_CerednikDrinfeld_ODModuleFrobeniusTwist
import Theorems.Thm_CerednikDrinfeld_FormalODModule_isCanonicalLMap_iff_isCanonicalLMap_comp_of_comp_frobenius
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius

set_option autoImplicit false

open CerednikDrinfeld

namespace SShift
open CerednikDrinfeld
variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}

def relabel (D : GradedCartierModuleData p B j) (j' : Zp2 p →+* B)
    (piece' : Fin 2 → Submodule (WittVector p B) D.M)
    (hc' : IsCompl (piece' 0) (piece' 1))
    (hVm : ∀ (i : Fin 2) (x : D.M), x ∈ piece' i → D.verschiebung x ∈ piece' (i + 1))
    (hFm : ∀ (i : Fin 2) (x : D.M), x ∈ piece' i → D.frobenius x ∈ piece' (i + 1))
    (hPm : ∀ (i : Fin 2) (x : D.M), x ∈ piece' i → D.varpi x ∈ piece' (i + 1)) :
    GradedCartierModuleData p B j' where
  M := D.M
  frobenius := D.frobenius
  verschiebung := D.verschiebung
  varpi := D.varpi
  piece := piece'
  frobenius_smul := D.frobenius_smul
  smul_verschiebung := D.smul_verschiebung
  verschiebung_smul_frobenius := D.verschiebung_smul_frobenius
  frobenius_verschiebung := D.frobenius_verschiebung
  varpi_verschiebung := D.varpi_verschiebung
  varpi_frobenius := D.varpi_frobenius
  varpi_varpi := D.varpi_varpi
  isCompl_piece := hc'
  verschiebung_mem := hVm
  frobenius_mem := hFm
  varpi_mem := hPm

theorem nVarpi_nMk {j₀ : Zp2 p →+* B} (D : GradedCartierModuleData p B j₀) (x y : D.M) :
    D.nVarpi (D.nMk (x, y)) = D.nMk (D.varpi x, D.varpi y) := rfl

theorem main (D : GradedCartierModuleData p B j) (j' : Zp2 p →+* B)
    (piece' : Fin 2 → Submodule (WittVector p B) D.M)
    (hc' : IsCompl (piece' 0) (piece' 1))
    (hVm : ∀ (i : Fin 2) (x : D.M), x ∈ piece' i → D.verschiebung x ∈ piece' (i + 1))
    (hFm : ∀ (i : Fin 2) (x : D.M), x ∈ piece' i → D.frobenius x ∈ piece' (i + 1))
    (hPm : ∀ (i : Fin 2) (x : D.M), x ∈ piece' i → D.varpi x ∈ piece' (i + 1))
    (hPiece : ∀ (i : Fin 2) (x : D.M), x ∈ piece' (i + 1) ↔ x ∈ D.piece i)
    (I : D.NMod →+ (SShift.relabel D j' piece' hc' hVm hFm hPm).NMod)
    (hI : ∀ x y : D.M, I (D.nMk (x, y)) = (SShift.relabel D j' piece' hc' hVm hFm hPm).nMk (x, y)) :
    Function.Bijective I ∧
    (∀ z, I (D.nVarpi z) = (SShift.relabel D j' piece' hc' hVm hFm hPm).nVarpi (I z)) ∧
    (∀ (i : Fin 2) (z : D.NMod), z ∈ D.nPiece i ↔ I z ∈ (SShift.relabel D j' piece' hc' hVm hFm hPm).nPiece (i + 1)) ∧
    (∀ (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L),
      ∃ hL' : (SShift.relabel D j' piece' hc' hVm hFm hPm).IsCartierLMap (I.comp L),
        (∀ (i : Fin 2) (z : D.NMod), z ∈ D.etaPiece L hL.map_verschiebung i ↔
          I z ∈ (SShift.relabel D j' piece' hc' hVm hFm hPm).etaPiece (I.comp L) hL'.map_verschiebung (i + 1))) := by
  classical

  have hinj : Function.Injective I := by
    intro z₁ z₂ h12
    obtain ⟨⟨a₁, b₁⟩, rfl⟩ := D.nMk_surjective z₁
    obtain ⟨⟨a₂, b₂⟩, rfl⟩ := D.nMk_surjective z₂
    rw [hI, hI] at h12
    rw [← sub_eq_zero, ← map_sub] at h12 ⊢

    rw [Prod.mk_sub_mk] at h12 ⊢
    rw [GradedCartierModuleData.nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h12 ⊢
    exact h12
  have hsurj : Function.Surjective I := by
    intro z'
    obtain ⟨⟨a, b⟩, rfl⟩ := (SShift.relabel D j' piece' hc' hVm hFm hPm).nMk_surjective z'
    exact ⟨D.nMk (a, b), hI a b⟩
  refine ⟨⟨hinj, hsurj⟩, ?_, ?_, ?_⟩
  ·
    intro z
    obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
    rw [nVarpi_nMk, hI, hI]
    rfl
  ·
    intro i z
    constructor
    · rintro ⟨⟨a, b⟩, hab, rfl⟩
      have hab' := AddSubgroup.mem_prod.mp hab
      exact ⟨(a, b), AddSubgroup.mem_prod.mpr ⟨(hPiece i a).2 hab'.1, (hPiece i b).2 hab'.2⟩, (hI a b).symm⟩
    · rintro ⟨⟨a, b⟩, hab, hz⟩
      have hab' := AddSubgroup.mem_prod.mp hab
      refine ⟨(a, b), AddSubgroup.mem_prod.mpr ⟨(hPiece i a).1 hab'.1, (hPiece i b).1 hab'.2⟩, hinj ?_⟩
      rw [hI]; exact hz
  ·
    intro L hL
    have hL' : (SShift.relabel D j' piece' hc' hVm hFm hPm).IsCartierLMap (I.comp L) := by
      refine ⟨?_, ?_, ?_⟩
      · intro w x
        have h1 : I (L (w • x)) = I (WittVector.frobenius w • L x) := congrArg I (hL.map_smul w x)
        refine h1.trans ?_
        obtain ⟨⟨a, b⟩, hab⟩ := D.nMk_surjective (L x)
        show I (WittVector.frobenius w • L x) = WittVector.frobenius w • I (L x)
        rw [← hab, GradedCartierModuleData.smul_nMk, hI, hI, GradedCartierModuleData.smul_nMk]
        rfl
      · intro x
        show I (L (D.verschiebung x)) = _
        rw [hL.map_verschiebung, hI]
        rfl
      · intro x
        show (SShift.relabel D j' piece' hc' hVm hFm hPm).lambda (I (L x)) = D.frobenius x
        rw [← hL.lambda_comp x]
        obtain ⟨⟨a, b⟩, hab⟩ := D.nMk_surjective (L x)
        rw [← hab, hI, GradedCartierModuleData.lambda_nMk, GradedCartierModuleData.lambda_nMk]
        rfl
    refine ⟨hL', ?_⟩
    ·
      intro i z
      have hphi : ∀ z, (SShift.relabel D j' piece' hc' hVm hFm hPm).phi (I.comp L) hL'.map_verschiebung (I z) = I (D.phi L hL.map_verschiebung z) := by
        intro z
        obtain ⟨⟨a, b⟩, rfl⟩ := D.nMk_surjective z
        rw [hI, GradedCartierModuleData.phi_nMk, GradedCartierModuleData.phi_nMk, map_add, hI]
        rfl
      have heta : z ∈ D.eta L hL.map_verschiebung ↔ I z ∈ (SShift.relabel D j' piece' hc' hVm hFm hPm).eta (I.comp L) hL'.map_verschiebung := by
        rw [GradedCartierModuleData.mem_eta_iff, GradedCartierModuleData.mem_eta_iff, hphi]
        exact ⟨fun h => by rw [h], fun h => hinj h⟩
      show z ∈ D.eta L hL.map_verschiebung ⊓ D.nPiece i ↔ I z ∈ (SShift.relabel D j' piece' hc' hVm hFm hPm).eta (I.comp L) hL'.map_verschiebung ⊓ (SShift.relabel D j' piece' hc' hVm hFm hPm).nPiece (i + 1)
      rw [AddSubgroup.mem_inf, AddSubgroup.mem_inf, heta]

      have hp2 : z ∈ D.nPiece i ↔ I z ∈ (SShift.relabel D j' piece' hc' hVm hFm hPm).nPiece (i + 1) := by
        constructor
        · rintro ⟨⟨a, b⟩, hab, rfl⟩
          have hab' := AddSubgroup.mem_prod.mp hab
          exact ⟨(a, b), AddSubgroup.mem_prod.mpr ⟨(hPiece i a).2 hab'.1, (hPiece i b).2 hab'.2⟩, (hI a b).symm⟩
        · rintro ⟨⟨a, b⟩, hab, hz⟩
          have hab' := AddSubgroup.mem_prod.mp hab
          refine ⟨(a, b), AddSubgroup.mem_prod.mpr ⟨(hPiece i a).1 hab'.1, (hPiece i b).1 hab'.2⟩, hinj ?_⟩
          rw [hI]; exact hz
      rw [hp2]

end SShift

theorem solution
    (p : ℕ) [Fact p.Prime] {C : Type} [CommRing C] (X : FormalODModule p C) (j : Zp2 p →+* C)
    (hc : IsCompl (X.gradedPiece j 0) (X.gradedPiece j 1))
    (hc' : IsCompl (X.gradedPiece (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) 0)
      (X.gradedPiece (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) 1))
    (I : (X.toGradedCartierModuleData j hc).NMod →+ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').NMod)
    (hI : ∀ x y : MvFormalGroup.CartierModule p X.F, I ((X.toGradedCartierModuleData j hc).nMk (x, y)) = (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').nMk (x, y)) :
    Function.Bijective I ∧
    (∀ z, I ((X.toGradedCartierModuleData j hc).nVarpi z) = (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').nVarpi (I z)) ∧
    (∀ (i : Fin 2) (z : (X.toGradedCartierModuleData j hc).NMod), z ∈ (X.toGradedCartierModuleData j hc).nPiece i ↔ I z ∈ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').nPiece (i + 1)) ∧
    (∀ (L : (X.toGradedCartierModuleData j hc).M →+ (X.toGradedCartierModuleData j hc).NMod) (hL : (X.toGradedCartierModuleData j hc).IsCartierLMap L),
      ∃ hL' : (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').IsCartierLMap (I.comp L),
        (∀ (i : Fin 2) (z : (X.toGradedCartierModuleData j hc).NMod), z ∈ (X.toGradedCartierModuleData j hc).etaPiece L hL.map_verschiebung i ↔
          I z ∈ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').etaPiece (I.comp L) hL'.map_verschiebung (i + 1)) ∧
        ((X.toGradedCartierModuleData j hc).IsCanonicalLMap L ↔ (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').IsCanonicalLMap (I.comp L))) := by
  obtain ⟨h1, h2, h3, h4⟩ := SShift.main (X.toGradedCartierModuleData j hc) (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p))
    (fun i => X.gradedSubmodule (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) (i : ℕ))
    (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').isCompl_piece (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').verschiebung_mem (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').frobenius_mem (X.toGradedCartierModuleData (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) hc').varpi_mem
    (by
      intro i x
      show x ∈ X.gradedPiece (j.comp (WittVector.frobenius : Zp2 p →+* Zp2 p)) ((i + 1 : Fin 2) : ℕ) ↔
        x ∈ X.gradedPiece j (i : ℕ)
      rw [FormalODModule.gradedPiece_fin_add_one, FormalODModule.gradedPiece_comp_frobenius, add_assoc,
        show (1 : ℕ) + 1 = 2 from rfl, FormalODModule.gradedPiece_add_two])
    I hI
  refine ⟨h1, h2, h3, fun L hL => ?_⟩
  obtain ⟨hL', h5⟩ := h4 L hL
  exact ⟨hL', h5, CerednikDrinfeld.FormalODModule.isCanonicalLMap_iff_isCanonicalLMap_comp_of_comp_frobenius p X j hc hc' I hI L hL hL'⟩

end S_CerednikDrinfeld_FormalODModule_nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_nMap_id_bijective_and_nPiece_and_eta_and_isCanonicalLMap_comp_frobenius (solution)
