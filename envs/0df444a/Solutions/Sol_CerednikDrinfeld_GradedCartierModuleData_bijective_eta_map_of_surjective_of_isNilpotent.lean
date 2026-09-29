-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.bijective_eta_map_of_surjective_of_isNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5d560b8b-1eef-5b05-8835-223a85cd2fed

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_surjective_of_isBaseChangeAlong_of_surjective
import Theorems.Thm_CerednikDrinfeld_GradedCartierModuleData_IsBaseChangeAlong_exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_bijective_eta_map_of_surjective_of_isNilpotent
p2m_attr_erase "instance" "MvFormalGroup.CartierModule.instAddCommGroup MvFormalGroup.CartierModule.instNeg MvFormalGroup.CartierModule.instAdd MvFormalGroup.CartierModule.instZero MvFormalGroup.WittLaw.instTendstoCofiniteProdMk MvFormalGroup.CartierModule.instModuleWittVector"
p2m_attr_erase "simp" "MvFormalGroup.CartierModule.toPowerSeries_verschiebungInt MvFormalGroup.WittLaw.xTaut_coeff MvFormalGroup.WittLaw.frobPolyFam_apply MvFormalGroup.CartierModule.toPowerSeries_sub MvFormalGroup.WittLaw.verFam_zero MvFormalGroup.WittLaw.verFam_succ MvFormalGroup.CartierModule.toPowerSeries_frobenius MvFormalGroup.CartierModule.toPowerSeries_verschiebung MvFormalGroup.WittLaw.blk_apply MvFormalGroup.WittLaw.weight_apply MvFormalGroup.CartierModule.toPowerSeries_map MvFormalGroup.CartierModule.toPowerSeries_precompFun MvFormalGroup.CartierModule.toPowerSeries_mapFun MvFormalGroup.CartierModule.mk.injEq MvFormalGroup.WittLaw.pairFam_apply MvFormalGroup.CartierModule.endAct_apply MvFormalGroup.WittLaw.frobFam_apply MvFormalGroup.CartierModule.toPowerSeries_zero MvFormalGroup.CartierModule.tangent_apply MvFormalGroup.CartierModule.toPowerSeries_precomp MvFormalGroup.CartierModule.Examples.toPowerSeries_addLinear MvFormalGroup.CartierModule.toPowerSeries_add MvFormalGroup.CartierModule.toPowerSeries_neg MvFormalGroup.CartierModule.mk.sizeOf_spec MvFormalGroup.CartierModule.inBlk_apply MvFormalGroup.WittLaw.teichFam_apply MvFormalGroup.CartierModule.toPowerSeries_homothety MvFormalGroup.WittLaw.verPoly_succ MvFormalGroup.WittLaw.xVec_coeff MvFormalGroup.WittLaw.cVec_coeff MvFormalGroup.WittLaw.cVec_mul MvFormalGroup.WittLaw.mulFam_apply MvFormalGroup.CartierModule.mapLinear_apply MvFormalGroup.WittLaw.cVec_add MvFormalGroup.WittLaw.cVec_zero MvFormalGroup.WittLaw.verPoly_zero MvFormalGroup.CartierModule.toPowerSeries_wittSMul MvFormalGroup.CartierModule.toPowerSeries_smul_witt MvFormalGroup.WittLaw.cVec_one"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace CerednikDrinfeld
p2m_export "CerednikDrinfeld" "Zp2 GradedCartierModuleData GradedCartierModuleData.IsBaseChangeAlong GradedCartierModuleData.exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective GradedCartierModuleData.bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero GradedCartierModuleData.existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule GradedCartierModuleData.surjective_of_isBaseChangeAlong_of_surjective GradedCartierModuleData.IsBaseChangeAlong.exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero"
namespace GradedCartierModuleData
p2m_export "CerednikDrinfeld.GradedCartierModuleData" "IsHomogeneousVBasis IsVAdicallyComplete IsSpecialCartierModule IsBaseChangeAlong isCompl_piece varpi mk M frobenius piece verschiebung NMod nMk_surjective nMap nMap_nMk IsBaseChangeAlong' IsCartierLMap IsCanonicalLMap eta exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule surjective_of_isBaseChangeAlong_of_surjective IsBaseChangeAlong.exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero"
namespace EtaNilpotent
p2m_open "CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld"

p2m_open "CerednikDrinfeld P2MW.S_CerednikDrinfeld_GradedCartierModuleData_bijective_eta_map_of_surjective_of_isNilpotent.CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData P2MW.S_CerednikDrinfeld_GradedCartierModuleData_bijective_eta_map_of_surjective_of_isNilpotent.CerednikDrinfeld.GradedCartierModuleData"

variable {p : ℕ} [Fact p.Prime]

theorem wmap_map {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T)
    (w : WittVector p R) : WittVector.map g (WittVector.map f w) = WittVector.map (g.comp f) w := by
  ext n
  simp only [WittVector.map_coeff, RingHom.comp_apply]

theorem nMap_comp_apply {B₁ B₂ B₃ : Type} [CommRing B₁] [CommRing B₂] [CommRing B₃]
    {j₁ : Zp2 p →+* B₁} {j₂ : Zp2 p →+* B₂} {j₃ : Zp2 p →+* B₃}
    (D₁ : GradedCartierModuleData p B₁ j₁) (D₂ : GradedCartierModuleData p B₂ j₂)
    (D₃ : GradedCartierModuleData p B₃ j₃)
    (f : D₁.M →+ D₂.M) (hfV : ∀ x, f (D₁.verschiebung x) = D₂.verschiebung (f x))
    (hfPi : ∀ x, f (D₁.varpi x) = D₂.varpi (f x))
    (g : D₂.M →+ D₃.M) (hgV : ∀ x, g (D₂.verschiebung x) = D₃.verschiebung (g x))
    (hgPi : ∀ x, g (D₂.varpi x) = D₃.varpi (g x))
    (hV : ∀ x, (g.comp f) (D₁.verschiebung x) = D₃.verschiebung ((g.comp f) x))
    (hPi : ∀ x, (g.comp f) (D₁.varpi x) = D₃.varpi ((g.comp f) x)) (z : D₁.NMod) :
    D₂.nMap D₃ g hgV hgPi (D₁.nMap D₂ f hfV hfPi z) = D₁.nMap D₃ (g.comp f) hV hPi z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D₁.nMk_surjective z
  rw [nMap_nMk, nMap_nMk, nMap_nMk]
  rfl

theorem nMap_congr {B₁ B₂ : Type} [CommRing B₁] [CommRing B₂]
    {j₁ : Zp2 p →+* B₁} {j₂ : Zp2 p →+* B₂}
    (D₁ : GradedCartierModuleData p B₁ j₁) (D₂ : GradedCartierModuleData p B₂ j₂)
    (f f' : D₁.M →+ D₂.M)
    (hV : ∀ x, f (D₁.verschiebung x) = D₂.verschiebung (f x))
    (hPi : ∀ x, f (D₁.varpi x) = D₂.varpi (f x))
    (hV' : ∀ x, f' (D₁.verschiebung x) = D₂.verschiebung (f' x))
    (hPi' : ∀ x, f' (D₁.varpi x) = D₂.varpi (f' x))
    (h : ∀ x, f x = f' x) (z : D₁.NMod) :
    D₁.nMap D₂ f hV hPi z = D₁.nMap D₂ f' hV' hPi' z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D₁.nMk_surjective z
  rw [nMap_nMk, nMap_nMk, h, h]

theorem exists_piece_decomp {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j) (x : D.M) :
    ∃ x₀ ∈ D.piece 0, ∃ x₁ ∈ D.piece 1, x = x₀ + x₁ := by
  have : x ∈ D.piece 0 ⊔ D.piece 1 := by
    rw [D.isCompl_piece.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 this
  exact ⟨y, hy, z, hz, rfl⟩

theorem eq_zero_of_mem_piece {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p B j) {x : D.M} (h₀ : x ∈ D.piece 0) (h₁ : x ∈ D.piece 1) : x = 0 :=
  Submodule.disjoint_def.1 D.isCompl_piece.disjoint x h₀ h₁

theorem isBaseChangeAlong'_comp {S B C : Type} [CommRing S] [CommRing B] [CommRing C]
    {jS : Zp2 p →+* S} {jB : Zp2 p →+* B} {jC : Zp2 p →+* C}
    (φ₀ : S →+* B) (π : B →+* C)
    (Dl : GradedCartierModuleData p S jS) (D : GradedCartierModuleData p B jB)
    (D₁ : GradedCartierModuleData p C jC)
    (f₀ : Dl.M →+ D.M) (hf₀ : IsBaseChangeAlong' φ₀ Dl D f₀)
    (g : D.M →+ D₁.M) (hg : IsBaseChangeAlong' π D D₁ g)
    (hbasis : ∀ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ → D₁.IsHomogeneousVBasis (fun i => g (γ i))) :
    IsBaseChangeAlong' (π.comp φ₀) Dl D₁ (g.comp f₀) := by
  obtain ⟨h1, h2, h3, h4, h5, γ, hγ, hfγ⟩ := hf₀
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := hg
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w x
    show g (f₀ (w • x)) = WittVector.map (π.comp φ₀) w • g (f₀ x)
    rw [h1, k1, wmap_map]
  · intro x
    show g (f₀ (Dl.frobenius x)) = D₁.frobenius (g (f₀ x))
    rw [h2, k2]
  · intro x
    show g (f₀ (Dl.verschiebung x)) = D₁.verschiebung (g (f₀ x))
    rw [h3, k3]
  · intro x
    show g (f₀ (Dl.varpi x)) = D₁.varpi (g (f₀ x))
    rw [h4, k4]
  · intro i x hx
    exact k5 i _ (h5 i x hx)
  · exact ⟨γ, hγ, hbasis _ hfγ⟩

theorem isCanonicalLMap_of_comp_eq {B C : Type} [CommRing B] [CommRing C] {j : Zp2 p →+* B}
    (π : B →+* C) (hπ : Function.Surjective π)
    (D : GradedCartierModuleData p B j) (D₁ : GradedCartierModuleData p C (π.comp j))
    (g : D.M →+ D₁.M) (hg : IsBaseChangeAlong π D D₁ g)
    (hbasis : ∀ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ → D₁.IsHomogeneousVBasis (fun i => g (γ i)))
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L₁ : D₁.M →+ D₁.NMod) (hL₁c : D₁.IsCartierLMap L₁)
    (hL₁g : ∀ x : D.M, L₁ (g x) = D.nMap D₁ g hg.2.2.1 hg.2.2.2.1 (L x)) :
    D₁.IsCanonicalLMap L₁ := by
  obtain ⟨S, instS, jS, φ₀, hφ₀, htf, Dl, hDl, f₀, hf₀, Ll, hLl, hcomp⟩ := hL.exists_lift
  have hg' : IsBaseChangeAlong' π D D₁ g := hg
  have hgf : IsBaseChangeAlong' (π.comp φ₀) Dl D₁ (g.comp f₀) :=
    isBaseChangeAlong'_comp φ₀ π Dl D D₁ f₀ hf₀ g hg' hbasis
  refine ⟨hL₁c, S, instS, jS, π.comp φ₀, hπ.comp hφ₀, htf, Dl, hDl, g.comp f₀, hgf, Ll, hLl, fun x => ?_⟩
  show L₁ (g (f₀ x)) = Dl.nMap D₁ (g.comp f₀) hgf.2.2.1 hgf.2.2.2.1 (Ll x)
  rw [hL₁g, hcomp]
  exact nMap_comp_apply Dl D D₁ f₀ _ _ g _ _ _ _ (Ll x)

section Factor

variable {B C B' : Type} [CommRing B] [CommRing C] [CommRing B']
  {j : Zp2 p →+* B} {j' : Zp2 p →+* B'}
  (π : B →+* C) (hπ : Function.Surjective π) (φ : B →+* B') (φbar : C →+* B')
  (hfac : ∀ b : B, φbar (π b) = φ b)
  (D : GradedCartierModuleData p B j) (D₁ : GradedCartierModuleData p C (π.comp j))
  (D' : GradedCartierModuleData p B' j')
  (g : D.M →+ D₁.M) (hg : IsBaseChangeAlong π D D₁ g) (hgs : Function.Surjective g)
  (f : D.M →+ D'.M) (hf : IsBaseChangeAlong' φ D D' f) (hD' : D'.IsVAdicallyComplete)

include hfac hg hf hD' in

theorem apply_eq_zero_of_apply_eq_zero {x : D.M} (hx : g x = 0) : f x = 0 := by
  obtain ⟨γ, hγ, hgγ⟩ := hg.2.2.2.2.2

  have hdiv : ∀ (n : ℕ) (y : D.M), g y = 0 → ∃ z : D'.M, f y = (⇑D'.verschiebung)^[n] z := by
    intro n
    induction n with
    | zero => intro y _; exact ⟨f y, rfl⟩
    | succ n ih =>
      intro y hy
      obtain ⟨c, y', hc, hy', rfl⟩ :=
        IsBaseChangeAlong.exists_eq_sum_teichmuller_smul_add_verschiebung_of_apply_eq_zero p j π D D₁ g
          hg γ hγ hgγ y hy
      obtain ⟨z, hz⟩ := ih y' hy'
      refine ⟨z, ?_⟩
      have hkill : ∀ i, f (WittVector.teichmuller p (c i) • γ i) = 0 := by
        intro i
        rw [hf.1, WittVector.map_teichmuller, ← hfac, hc, map_zero, WittVector.teichmuller_zero,
          zero_smul]
      rw [map_add, map_sum, Finset.sum_eq_zero (fun i _ => hkill i), zero_add, hf.2.2.1, hz,
        Function.iterate_succ_apply']

  obtain ⟨s, -, huniq⟩ := hD' (fun _ => (0 : D'.M))
  have hzero : ∀ n : ℕ, (⇑D'.verschiebung)^[n] (0 : D'.M) = 0 :=
    fun n => Function.iterate_fixed (map_zero D'.verschiebung) n
  have h1 : f x = s := huniq (f x) fun N => by
    obtain ⟨z, hz⟩ := hdiv N x hx
    exact ⟨z, by rw [Finset.sum_eq_zero (fun m _ => hzero m), zero_add]; exact hz⟩
  have h2 : (0 : D'.M) = s := huniq 0 fun N =>
    ⟨0, by rw [Finset.sum_eq_zero (fun m _ => hzero m), zero_add, hzero]⟩
  rw [h1, ← h2]

include hfac hg hf hD' in

def factor : D₁.M →+ D'.M where
  toFun y := f (Function.surjInv hgs y)
  map_zero' := by
    apply apply_eq_zero_of_apply_eq_zero π φ φbar hfac D D₁ D' g hg f hf hD'
    exact Function.surjInv_eq hgs 0
  map_add' y y' := by
    have h0 : g (Function.surjInv hgs (y + y') - Function.surjInv hgs y - Function.surjInv hgs y') = 0 := by
      rw [map_sub, map_sub, Function.surjInv_eq hgs, Function.surjInv_eq hgs, Function.surjInv_eq hgs]
      abel
    have := apply_eq_zero_of_apply_eq_zero π φ φbar hfac D D₁ D' g hg f hf hD' h0
    rw [map_sub, map_sub] at this

    have := sub_eq_zero.1 this
    rw [sub_eq_iff_eq_add] at this
    rw [this, add_comm]

theorem factor_apply (x : D.M) :
    factor π φ φbar hfac D D₁ D' g hg hgs f hf hD' (g x) = f x := by
  show f (Function.surjInv hgs (g x)) = f x
  have h0 : g (Function.surjInv hgs (g x) - x) = 0 := by
    rw [map_sub, Function.surjInv_eq hgs, sub_self]
  have := apply_eq_zero_of_apply_eq_zero π φ φbar hfac D D₁ D' g hg f hf hD' h0
  rwa [map_sub, sub_eq_zero] at this

include hπ in

theorem factor_isBaseChangeAlong'
    (hbasis : ∀ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ → D₁.IsHomogeneousVBasis (fun i => g (γ i))) :
    IsBaseChangeAlong' φbar D₁ D' (factor π φ φbar hfac D D₁ D' g hg hgs f hf hD') := by
  set h := factor π φ φbar hfac D D₁ D' g hg hgs f hf hD' with hdef
  have happ : ∀ x, h (g x) = f x := factor_apply π φ φbar hfac D D₁ D' g hg hgs f hf hD'
  have k1 := hg.1
  have k2 := hg.2.1
  have k3 := hg.2.2.1
  have k4 := hg.2.2.2.1
  have k5 := hg.2.2.2.2.1
  have h1 := hf.1
  have h2 := hf.2.1
  have h3 := hf.2.2.1
  have h4 := hf.2.2.2.1
  have h5 := hf.2.2.2.2.1
  obtain ⟨γ, hγ, hfγ⟩ := hf.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro wbar y
    obtain ⟨w, rfl⟩ := WittVector.map_surjective π hπ wbar
    obtain ⟨x, rfl⟩ := hgs y
    rw [← k1, happ, happ, h1, wmap_map]
    congr 1
    congr 1
    ext n
    simp only [WittVector.map_coeff, RingHom.comp_apply, hfac]
  · intro y
    obtain ⟨x, rfl⟩ := hgs y
    rw [← k2, happ, happ, h2]
  · intro y
    obtain ⟨x, rfl⟩ := hgs y
    rw [← k3, happ, happ, h3]
  · intro y
    obtain ⟨x, rfl⟩ := hgs y
    rw [← k4, happ, happ, h4]
  · intro i y hy

    obtain ⟨x, rfl⟩ := hgs y
    obtain ⟨x₀, hx₀, x₁, hx₁, rfl⟩ := exists_piece_decomp D x
    have hg₀ : g x₀ ∈ D₁.piece 0 := k5 0 x₀ hx₀
    have hg₁ : g x₁ ∈ D₁.piece 1 := k5 1 x₁ hx₁
    have hi : i = 0 ∨ i = 1 := by
      rcases i with ⟨i, hi⟩
      rcases i with _ | i
      · left; rfl
      · rcases i with _ | i
        · right; rfl
        · omega
    rcases hi with rfl | rfl
    ·
      have : g x₁ = 0 := by
        refine eq_zero_of_mem_piece D₁ ?_ hg₁
        have := Submodule.sub_mem _ hy hg₀
        rwa [map_add, add_sub_cancel_left] at this
      rw [map_add, this, add_zero, happ]
      exact h5 0 x₀ hx₀
    · have : g x₀ = 0 := by
        refine eq_zero_of_mem_piece D₁ hg₀ ?_
        have := Submodule.sub_mem _ hy hg₁
        rwa [map_add, add_sub_cancel_right] at this
      rw [map_add, this, zero_add, happ]
      exact h5 1 x₁ hx₁
  · refine ⟨fun i => g (γ i), hbasis γ hγ, ?_⟩
    have : (fun i => h (g (γ i))) = fun i => f (γ i) := funext fun i => happ _
    rw [this]; exact hfγ

end Factor

def Holds (p : ℕ) [Fact p.Prime] (P : ∀ (B : Type) [CommRing B], Ideal B → Prop) : Prop :=
  ∀ (B B' : Type) [CommRing B] [CommRing B'] (j : Zp2 p →+* B) (j' : Zp2 p →+* B') (φ : B →+* B')
    (hj : φ.comp j = j') (hφ : Function.Surjective φ) (hP : P B (RingHom.ker φ))
    (D : GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : GradedCartierModuleData p B' j') (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : IsBaseChangeAlong' φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L')
    (hLL' : ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x)),
    Set.BijOn (D.nMap D' f hf.2.2.1 hf.2.2.2.1)
      (D.eta L hL.isCartierLMap.map_verschiebung : Set D.NMod)
      (D'.eta L' hL'.isCartierLMap.map_verschiebung : Set D'.NMod)

theorem holds_mono {P P' : ∀ (B : Type) [CommRing B], Ideal B → Prop}
    (h : ∀ (B : Type) [CommRing B] (I : Ideal B), P B I → P' B I) (hP' : Holds p P') : Holds p P :=
  fun B B' _ _ j j' φ hj hφ hP => hP' B B' j j' φ hj hφ (h B _ hP)

theorem holds_step : Holds p (fun B _ I => I * I = ⊥ ∧ ∀ x ∈ I, (p : B) * x = 0) := by
  intro B B' _ _ j j' φ hj hφ hP D hD D' hD' f hf L hL L' hL' hLL'
  subst hj
  exact bijOn_nMap_eta_of_sq_eq_zero_of_mul_eq_zero p j φ hφ hP.1 hP.2 D hD D' hD' f hf L hL L' hL' hLL'

theorem holds_bot : Holds p (fun B _ I => I = ⊥) := by
  refine holds_mono (fun B _ I hI => ?_) holds_step
  subst hI
  exact ⟨by simp, fun x hx => by rw [(Submodule.mem_bot _).1 hx, mul_zero]⟩

theorem holds_split {P P₁ P₂ : ∀ (B : Type) [CommRing B], Ideal B → Prop}
    (h₁ : Holds p P₁) (h₂ : Holds p P₂)
    (hs : ∀ (B : Type) [CommRing B] (I : Ideal B), P B I →
      ∃ J : Ideal B, J ≤ I ∧ P₁ B J ∧ P₂ (B ⧸ J) (I.map (Ideal.Quotient.mk J))) :
    Holds p P := by
  intro B B' _ _ j j' φ hj hφ hP D hD D' hD' f hf L hL L' hL' hLL'
  obtain ⟨J, hJI, hP₁, hP₂⟩ := hs B (RingHom.ker φ) hP

  set π : B →+* B ⧸ J := Ideal.Quotient.mk J with hπdef
  have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
  have hkerπ : RingHom.ker π = J := Ideal.mk_ker

  obtain ⟨D₁, g, hD₁, hg, hbasis⟩ :=
    exists_isSpecialCartierModule_and_isBaseChangeAlong_of_surjective p j π hπ D hD
  have hgs : Function.Surjective g :=
    surjective_of_isBaseChangeAlong_of_surjective p j π hπ D hD D₁ hD₁ g hg
  have hg' : IsBaseChangeAlong' π D D₁ g := hg

  obtain ⟨L₁, ⟨hL₁g, hL₁c⟩, -⟩ :=
    existsUnique_comp_eq_nMap_comp_and_isCartierLMap_of_surjective_of_isSpecialCartierModule
      p j π hπ D hD D₁ hD₁ g hg L hL.isCartierLMap
  have hL₁ : D₁.IsCanonicalLMap L₁ :=
    isCanonicalLMap_of_comp_eq π hπ D D₁ g hg hbasis L hL L₁ hL₁c hL₁g

  have hP₁' : P₁ B (RingHom.ker π) := by rw [hkerπ]; exact hP₁
  have bij₁ := h₁ B (B ⧸ J) j (π.comp j) π rfl hπ hP₁' D hD D₁ hD₁ g hg' L hL L₁ hL₁ hL₁g

  set φbar : B ⧸ J →+* B' := Ideal.Quotient.lift J φ (fun b hb => hJI hb) with hφbardef
  have hfac : ∀ b, φbar (π b) = φ b := fun b => Ideal.Quotient.lift_mk J φ _
  have hφbar : Function.Surjective φbar := by
    intro y
    obtain ⟨b, rfl⟩ := hφ y
    exact ⟨π b, hfac b⟩
  have hkerbar : RingHom.ker φbar = (RingHom.ker φ).map π := by
    ext y
    obtain ⟨b, rfl⟩ := hπ y
    rw [RingHom.mem_ker, hfac, Ideal.mem_map_iff_of_surjective π hπ]
    constructor
    · intro hb; exact ⟨b, hb, rfl⟩
    · rintro ⟨x, hx, hxb⟩
      have : x - b ∈ J := by
        rw [← hkerπ, RingHom.mem_ker, map_sub, hxb, sub_self]
      have hxb' : φ (x - b) = 0 := hJI this
      rw [map_sub, sub_eq_zero] at hxb'
      rw [← hxb']; exact hx
  have hj' : φbar.comp (π.comp j) = j' := by
    rw [← hj]
    ext x
    simp only [RingHom.comp_apply, hfac]

  set h := factor π φ φbar hfac D D₁ D' g hg hgs f hf hD'.2 with hhdef
  have happ : ∀ x, h (g x) = f x := factor_apply π φ φbar hfac D D₁ D' g hg hgs f hf hD'.2
  have hh : IsBaseChangeAlong' φbar D₁ D' h :=
    factor_isBaseChangeAlong' π hπ φ φbar hfac D D₁ D' g hg hgs f hf hD'.2 hbasis

  have hNcomp : ∀ z : D.NMod, D₁.nMap D' h hh.2.2.1 hh.2.2.2.1 (D.nMap D₁ g hg.2.2.1 hg.2.2.2.1 z) =
      D.nMap D' f hf.2.2.1 hf.2.2.2.1 z := by
    intro z
    have hVc : ∀ x, (h.comp g) (D.verschiebung x) = D'.verschiebung ((h.comp g) x) := by
      intro x; show h (g (D.verschiebung x)) = D'.verschiebung (h (g x))
      rw [hg.2.2.1, hh.2.2.1]
    have hPic : ∀ x, (h.comp g) (D.varpi x) = D'.varpi ((h.comp g) x) := by
      intro x; show h (g (D.varpi x)) = D'.varpi (h (g x))
      rw [hg.2.2.2.1, hh.2.2.2.1]
    rw [nMap_comp_apply D D₁ D' g _ _ h _ _ hVc hPic z]
    exact nMap_congr D D' (h.comp g) f hVc hPic _ _ (fun x => happ x) z

  have hLL'₁ : ∀ y : D₁.M, L' (h y) = D₁.nMap D' h hh.2.2.1 hh.2.2.2.1 (L₁ y) := by
    intro y
    obtain ⟨x, rfl⟩ := hgs y
    rw [happ, hLL', hL₁g, hNcomp]

  have hP₂' : P₂ (B ⧸ J) (RingHom.ker φbar) := by rw [hkerbar]; exact hP₂
  have bij₂ := h₂ (B ⧸ J) B' (π.comp j) j' φbar hj' hφbar hP₂' D₁ hD₁ D' hD' h hh L₁ hL₁ L' hL' hLL'₁

  have hcomp := bij₂.comp bij₁
  refine (Set.EqOn.bijOn_iff (fun z _ => ?_)).1 hcomp
  exact hNcomp z

theorem holds_sqZero (b : ℕ) :
    Holds p (fun B _ I => I * I = ⊥ ∧ ∀ x ∈ I, (p : B) ^ b * x = 0) := by
  induction b with
  | zero =>
    refine holds_mono (fun B _ I hI => ?_) holds_bot
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := hI.2 x hx
    rwa [pow_zero, one_mul] at this
  | succ b ih =>
    refine holds_split holds_step ih (fun B _ I hI => ?_)
    obtain ⟨hI2, hIp⟩ := hI
    refine ⟨Ideal.span {((p : B)) ^ b} * I, Ideal.mul_le_right, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rw [eq_bot_iff]
      calc Ideal.span {((p : B)) ^ b} * I * (Ideal.span {((p : B)) ^ b} * I) ≤ I * I :=
            Ideal.mul_mono Ideal.mul_le_right Ideal.mul_le_right
        _ = ⊥ := hI2
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Ideal.mem_span_singleton_mul.1 hx
      rw [← mul_assoc, ← pow_succ']
      exact hIp y hy
    · rw [← Ideal.map_mul, hI2, Ideal.map_bot]
    · intro x hx
      obtain ⟨y, hy, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective).1 hx
      rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {((p : B)) ^ b} * I)) p, ← map_pow, ← map_mul,
        Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hy

theorem holds_sqZero' :
    Holds p (fun B _ I => I * I = ⊥ ∧ ∃ b : ℕ, ∀ x ∈ I, (p : B) ^ b * x = 0) := by
  intro B B' _ _ j j' φ hj hφ hP
  obtain ⟨h2, b, hb⟩ := hP
  exact holds_sqZero b B B' j j' φ hj hφ ⟨h2, hb⟩

theorem holds_nilpotent (a : ℕ) :
    Holds p (fun B _ I => I ^ (a + 1) = ⊥ ∧ ∃ b : ℕ, ∀ x ∈ I, (p : B) ^ b * x = 0) := by
  induction a with
  | zero =>
    refine holds_mono (fun B _ I hI => ?_) holds_bot
    simpa using hI.1
  | succ a ih =>
    refine holds_split holds_sqZero' ih (fun B _ I hI => ?_)
    obtain ⟨hIa, b, hb⟩ := hI
    refine ⟨I ^ (a + 1), Ideal.pow_le_self (Nat.succ_ne_zero a), ⟨?_, b, ?_⟩, ⟨?_, b, ?_⟩⟩
    · rw [eq_bot_iff, ← pow_two, ← pow_mul]
      calc I ^ ((a + 1) * 2) ≤ I ^ (a + 1 + 1) := Ideal.pow_le_pow_right (by omega)
        _ = ⊥ := hIa
    · intro x hx
      exact hb x (Ideal.pow_le_self (Nat.succ_ne_zero a) hx)
    · rw [← Ideal.map_pow, Ideal.map_quotient_self]
    · intro x hx
      obtain ⟨y, hy, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective).1 hx
      rw [← map_natCast (Ideal.Quotient.mk (I ^ (a + 1))) p, ← map_pow, ← map_mul, hb y hy, map_zero]

end CerednikDrinfeld.GradedCartierModuleData.EtaNilpotent

end

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_bijective_eta_map_of_surjective_of_isNilpotent.CerednikDrinfeld _root_.CerednikDrinfeld.GradedCartierModuleData _root_.P2MW.S_CerednikDrinfeld_GradedCartierModuleData_bijective_eta_map_of_surjective_of_isNilpotent.CerednikDrinfeld.GradedCartierModuleData CerednikDrinfeld.GradedCartierModuleData.EtaNilpotent in

theorem solution
    (p : ℕ) [Fact p.Prime] {B B' : Type} [CommRing B] [CommRing B']
    (j : CerednikDrinfeld.Zp2 p →+* B) (φ : B →+* B') (hφ : Function.Surjective φ)
    (hI : IsNilpotent (RingHom.ker φ)) (hIp : ∃ b : ℕ, ∀ x ∈ RingHom.ker φ, (p : B) ^ b * x = 0)
    (D : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (D' : CerednikDrinfeld.GradedCartierModuleData p B' (φ.comp j)) (hD' : D'.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong φ D D' f)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L)
    (L' : D'.M →+ D'.NMod) (hL' : D'.IsCanonicalLMap L')
    (hLL' : ∀ x : D.M, L' (f x) = D.nMap D' f hf.2.2.1 hf.2.2.2.1 (L x)) :
    Set.BijOn (D.nMap D' f hf.2.2.1 hf.2.2.2.1)
      (D.eta L hL.isCartierLMap.map_verschiebung : Set D.NMod)
      (D'.eta L' hL'.isCartierLMap.map_verschiebung : Set D'.NMod) := by
  obtain ⟨a, ha⟩ := hI
  have hf' : IsBaseChangeAlong' φ D D' f := hf
  have hP : (RingHom.ker φ) ^ (a + 1) = ⊥ ∧ ∃ b : ℕ, ∀ x ∈ RingHom.ker φ, (p : B) ^ b * x = 0 := by
    refine ⟨?_, hIp⟩
    rw [pow_succ, ha, zero_mul]
    rfl
  exact holds_nilpotent (p := p) a B B' j (φ.comp j) φ rfl hφ hP D hD D' hD' f hf' L hL L' hL' hLL'

end S_CerednikDrinfeld_GradedCartierModuleData_bijective_eta_map_of_surjective_of_isNilpotent
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_bijective_eta_map_of_surjective_of_isNilpotent (solution)
