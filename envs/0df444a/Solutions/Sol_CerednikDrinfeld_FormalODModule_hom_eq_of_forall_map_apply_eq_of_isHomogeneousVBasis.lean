-- Prove2me | solution 1 for CerednikDrinfeld.FormalODModule.hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/7be2b75e-7063-58e0-ad99-8e2b0fe2be4f

import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP
import Theorems.Thm_MvFormalGroup_CartierModule_eq_of_map_eq
import Theorems.Thm_MvFormalGroup_CartierModule_existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add
import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_CartierStructureConstants
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalODModule_hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis
p2m_attr_erase "simp" "MvPowerSeries.blockPermEmbed_apply"

set_option autoImplicit false

open CerednikDrinfeld MvFormalGroup MvFormalGroup.CartierModule

namespace HomExtVBasis

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B]

theorem map_iterate_verschiebungInt {d d' : ℕ} {Φ : MvFormalGroup d B} {Φ' : MvFormalGroup d' B}
    [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') (n : ℕ) (f : CartierModule p Φ) :
    map φ ((⇑(verschiebungInt (p := p) (Φ := Φ)))^[n] f) =
      (⇑(verschiebungInt (p := p) (Φ := Φ')))^[n] (map φ f) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_verschiebungInt, ih]

theorem iterate_verschiebungInt_sub {d : ℕ} {Φ : MvFormalGroup d B} [Φ.IsComm] (n : ℕ) (f g : CartierModule p Φ) :
    (⇑(verschiebungInt (p := p) (Φ := Φ)))^[n] (f - g) =
      (⇑(verschiebungInt (p := p) (Φ := Φ)))^[n] f - (⇑(verschiebungInt (p := p) (Φ := Φ)))^[n] g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih, map_sub]

theorem iterate_verschiebungInt_zero {d : ℕ} {Φ : MvFormalGroup d B} [Φ.IsComm] (n : ℕ) :
    (⇑(verschiebungInt (p := p) (Φ := Φ)))^[n] 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, map_zero]

theorem hom_eq_of_forall_map_eq_of_isUnit_det [CharP B p] {d d' : ℕ}
    (Φ : MvFormalGroup d B) [Φ.IsComm] (Φ' : MvFormalGroup d' B) [Φ'.IsComm]
    (f : Fin d → CartierModule p Φ) (hf : IsUnit (Matrix.of fun i j => tangent (f i) j).det)
    (φ ψ : Φ.Hom Φ') (h : ∀ i, map φ (f i) = map ψ (f i)) : φ = ψ := by
  apply MvFormalGroup.CartierModule.eq_of_map_eq p Φ Φ' φ ψ
  intro g

  have hdiv : ∀ N : ℕ, ∃ t : CartierModule p Φ',
      map φ g - map ψ g = (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ')))^[m] ((fun _ => (0 : CartierModule p Φ')) m)) +
        (⇑(verschiebungInt (p := p) (Φ := Φ')))^[N] t := by
    intro N
    obtain ⟨⟨c, hN⟩, hg, -⟩ :=
      MvFormalGroup.CartierModule.existsUnique_eq_sum_verschiebungInt_iterate_homothety_add_of_charP p Φ f hf g N
    refine ⟨map φ hN - map ψ hN, ?_⟩
    have hsum0 : (∑ m ∈ Finset.range N, (⇑(verschiebungInt (p := p) (Φ := Φ')))^[m] ((fun _ => (0 : CartierModule p Φ')) m)) = 0 :=
      Finset.sum_eq_zero fun m _ => iterate_verschiebungInt_zero m
    have hφ : map φ g = (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ')))^[(m : ℕ)]
        (∑ i : Fin d, homothety (c m i) (map φ (f i)))) + (⇑(verschiebungInt (p := p) (Φ := Φ')))^[N] (map φ hN) := by
      conv_lhs => rw [hg]
      rw [map_add, map_sum, map_iterate_verschiebungInt]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_iterate_verschiebungInt, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_homothety]
    have hψ : map ψ g = (∑ m : Fin N, (⇑(verschiebungInt (p := p) (Φ := Φ')))^[(m : ℕ)]
        (∑ i : Fin d, homothety (c m i) (map ψ (f i)))) + (⇑(verschiebungInt (p := p) (Φ := Φ')))^[N] (map ψ hN) := by
      conv_lhs => rw [hg]
      rw [map_add, map_sum, map_iterate_verschiebungInt]
      congr 1
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_iterate_verschiebungInt, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_homothety]
    simp_rw [← h] at hψ
    rw [hsum0, zero_add, hφ, hψ, add_sub_add_left_eq_sub, iterate_verschiebungInt_sub]

  obtain ⟨s, hs, huniq⟩ :=
    MvFormalGroup.CartierModule.existsUnique_forall_eq_sum_range_verschiebungInt_iterate_add p Φ' (fun _ => (0 : CartierModule p Φ'))
  have h1 : map φ g - map ψ g = s := huniq _ hdiv
  have h0 : (0 : CartierModule p Φ') = s := huniq _ fun N => ⟨0, by
    rw [iterate_verschiebungInt_zero, add_zero]
    exact (Finset.sum_eq_zero fun m _ => iterate_verschiebungInt_zero m).symm⟩
  exact sub_eq_zero.mp (h1.trans h0.symm)

end HomExtVBasis

theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] [CharP B p] (j : CerednikDrinfeld.Zp2 p →+* B)
    (X : CerednikDrinfeld.FormalODModule p B) {d' : ℕ} (G : MvFormalGroup d' B) [G.IsComm]
    (γ : Fin 2 → MvFormalGroup.CartierModule p X.F) (hγ : X.IsHomogeneousVBasis j γ)
    (φ ψ : MvFormalGroup.Hom X.F G)
    (h : ∀ i : Fin 2, MvFormalGroup.CartierModule.map φ (γ i) = MvFormalGroup.CartierModule.map ψ (γ i)) :
    φ = ψ := by
  exact HomExtVBasis.hom_eq_of_forall_map_eq_of_isUnit_det X.F G γ hγ.2 φ ψ h

end S_CerednikDrinfeld_FormalODModule_hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis
end P2MW
export P2MW.S_CerednikDrinfeld_FormalODModule_hom_eq_of_forall_map_apply_eq_of_isHomogeneousVBasis (solution)
