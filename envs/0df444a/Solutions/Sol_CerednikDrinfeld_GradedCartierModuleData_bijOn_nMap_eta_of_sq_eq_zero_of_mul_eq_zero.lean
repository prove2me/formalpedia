-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/59840f9c-bb60-5d6d-a1ed-97e3c57c0da3

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_phi_iterate_three_eq_zero_of_nMap_eq_zero_of_sq_eq_zero
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_surjective_of_isBaseChangeAlong_of_surjective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_verschiebungInt MvFormalGroup.WittLaw.xTaut_coeff MvFormalGroup.WittLaw.frobPolyFam_apply MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one"

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData in
theorem solution
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    (j : CerednikDrinfeld.Zp2 p →+* B) (φ : B →+* B') (hφ : Function.Surjective φ)
    (hI2 : RingHom.ker φ * RingHom.ker φ = ⊥) (hIp : ∀ x ∈ RingHom.ker φ, (p : B) * x = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j)) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L')
    (hLL' : ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x)) :
    Set.BijOn (D.nMap D' f hf.2.2.1 hf.2.2.2.1)
      (D.eta L hL.isCartierLMap.map_verschiebung : Set D.NMod)
      (D'.eta L' hL'.isCartierLMap.map_verschiebung : Set D'.NMod) := by
  set hLV := hL.isCartierLMap.map_verschiebung
  set hLV' := hL'.isCartierLMap.map_verschiebung
  set Nf := D.nMap D' f hf.2.2.1 hf.2.2.2.1 with hNf

  have comm : ∀ z : D.NMod, D'.phi L' hLV' (Nf z) = Nf (D.phi L hLV z) := by
    intro z
    obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective z
    rw [hNf, nMap_nMk, phi_nMk, phi_nMk, map_add, nMap_nMk, map_zero, hLL']

  have c7 : ∀ z : D.NMod, Nf z = 0 →
      Nf (D.phi L hLV z) = 0 ∧ D.phi L hLV (D.phi L hLV (D.phi L hLV z)) = 0 :=
    fun z hz =>
      CerednikDrinfeld.GradedCartierModuleData.phi_iterate_three_eq_zero_of_nMap_eq_zero_of_sq_eq_zero
        p j φ hφ hI2 hIp D hD D' hD' f hf L hL z hz

  have fsurj : Function.Surjective f :=
    CerednikDrinfeld.GradedCartierModuleData.surjective_of_isBaseChangeAlong_of_surjective
      p j φ hφ D hD D' hD' f hf
  have surj : Function.Surjective Nf := by
    intro z'
    obtain ⟨⟨a', b'⟩, rfl⟩ := D'.nMk_surjective z'
    obtain ⟨a, rfl⟩ := fsurj a'
    obtain ⟨b, rfl⟩ := fsurj b'
    exact ⟨D.nMk (a, b), by rw [hNf, nMap_nMk]⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    intro z hz
    rw [SetLike.mem_coe, mem_eta_iff] at hz ⊢
    rw [comm, hz]
  ·
    intro z₁ hz₁ z₂ hz₂ h
    rw [SetLike.mem_coe, mem_eta_iff] at hz₁ hz₂
    have hd : Nf (z₁ - z₂) = 0 := by rw [map_sub, sub_eq_zero]; exact h
    have hfix : D.phi L hLV (z₁ - z₂) = z₁ - z₂ := by rw [map_sub, hz₁, hz₂]
    have h3 := (c7 _ hd).2
    rw [hfix, hfix, hfix] at h3
    exact sub_eq_zero.mp h3
  ·
    intro z' hz'
    rw [SetLike.mem_coe, mem_eta_iff] at hz'
    obtain ⟨z₀, hz₀⟩ := surj z'
    set w := D.phi L hLV z₀ - z₀ with hw
    have hw0 : Nf w = 0 := by
      rw [hw, map_sub, ← comm, hz₀, hz', sub_self]
    have hw1 := (c7 w hw0).1
    have hw2 := (c7 _ hw1).1
    have hw3 := (c7 w hw0).2
    refine ⟨z₀ + (w + D.phi L hLV w + D.phi L hLV (D.phi L hLV w)), ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_eta_iff, map_add, map_add, map_add, hw3, add_zero, hw]
      abel
    · rw [map_add, map_add, map_add, hz₀, hw0, hw1, hw2, add_zero, add_zero, add_zero]

end S_CerednikDrinfeld_GradedCartierModuleData_bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero (solution)
