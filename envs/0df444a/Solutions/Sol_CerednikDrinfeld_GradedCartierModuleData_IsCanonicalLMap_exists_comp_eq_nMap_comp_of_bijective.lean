-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.IsCanonicalLMap.exists_comp_eq_nMap_comp_of_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/a38febae-baf1-5f3e-90cf-b8a8e1e052d6

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_comp_eq_nMap_comp_of_bijective

set_option autoImplicit false

noncomputable section

namespace P2mIsoL

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}

theorem nMap_smul (D D' : GradedCartierModuleData p B j) (f : D.M →+ D'.M)
    (hW : ∀ (w : WittVector p B) (x : D.M), f (w • x) = w • f x)
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (w : WittVector p B) (z : D.NMod) :
    D.nMap D' f hV hPi (w • z) = w • D.nMap D' f hV hPi z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nMk_surjective z
  rw [smul_nMk, nMap_nMk, nMap_nMk, smul_nMk, hW, hW]

theorem nMap_nMap {B'' : Type} [CommRing B''] {j'' : Zp2 p →+* B''}
    (D₁ : GradedCartierModuleData p B'' j'') (D D' : GradedCartierModuleData p B j)
    (g : D₁.M →+ D.M) (hgV : ∀ x, g (D₁.verschiebung x) = D.verschiebung (g x))
    (hgPi : ∀ x, g (D₁.varpi x) = D.varpi (g x))
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hcV : ∀ x, (f.comp g) (D₁.verschiebung x) = D'.verschiebung ((f.comp g) x))
    (hcPi : ∀ x, (f.comp g) (D₁.varpi x) = D'.varpi ((f.comp g) x)) (z : D₁.NMod) :
    D.nMap D' f hV hPi (D₁.nMap D g hgV hgPi z) = D₁.nMap D' (f.comp g) hcV hcPi z := by
  obtain ⟨⟨m, m'⟩, rfl⟩ := D₁.nMk_surjective z
  rw [nMap_nMk, nMap_nMk, nMap_nMk]
  rfl

theorem isHomogeneousVBasis_of_bijective (D D' : GradedCartierModuleData p B j) (f : D.M →+ D'.M)
    (hf : Function.Bijective f)
    (hW : ∀ (w : WittVector p B) (x : D.M), f (w • x) = w • f x)
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hpc : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (γ : Fin 2 → D.M) (hγ : D.IsHomogeneousVBasis γ) :
    D'.IsHomogeneousVBasis (fun i => f (γ i)) := by
  refine ⟨fun i => hpc i _ (hγ.1 i), fun x' => ?_⟩
  obtain ⟨x, rfl⟩ := hf.2 x'
  obtain ⟨cy, hcy, huniq⟩ := hγ.2 x
  have hform : ∀ (c : Fin 2 → B) (y : D.M),
      f ((∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + D.verschiebung y) =
        (∑ i : Fin 2, WittVector.teichmuller p (c i) • f (γ i)) + D'.verschiebung (f y) := by
    intro c y
    rw [map_add, map_sum, hV]
    congr 1
    exact Finset.sum_congr rfl fun i _ => hW _ _
  refine ⟨(cy.1, f cy.2), ?_, ?_⟩
  · show f x = (∑ i : Fin 2, WittVector.teichmuller p (cy.1 i) • f (γ i)) + D'.verschiebung (f cy.2)
    rw [← hform, ← hcy]
  · rintro ⟨c, y'⟩ h
    obtain ⟨y, rfl⟩ := hf.2 y'
    have hx : x = (∑ i : Fin 2, WittVector.teichmuller p (c i) • γ i) + D.verschiebung y := by
      apply hf.1
      rw [hform]; exact h
    have := huniq (c, y) hx
    show (c, f y) = (cy.1, f cy.2)
    rw [show c = cy.1 from congrArg Prod.fst this, show y = cy.2 from congrArg Prod.snd this]

end P2mIsoL

end

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData P2mIsoL in
theorem solution
    (p : ℕ) [Fact p.Prime] {B : Type} [CommRing B] (j : CerednikDrinfeld.Zp2 p →+* B)
    (D D' : CerednikDrinfeld.GradedCartierModuleData p B j) (hD : D.IsSpecialCartierModule)
    (f : D.M →+ D'.M) (hf : Function.Bijective f)
    (hW : ∀ (w : WittVector p B) (x : D.M), f (w • x) = w • f x)
    (hF : ∀ x, f (D.frobenius x) = D'.frobenius (f x))
    (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x))
    (hpc : ∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i)
    (L : D.M →+ D.NMod) (hL : D.IsCanonicalLMap L) :
    ∃ L' : D'.M →+ D'.NMod, D'.IsCanonicalLMap L' ∧
      ∀ x : D.M, L' (f x) = D.nMap D' f hV hPi (L x) := by
  classical

  let e : D.M ≃+ D'.M := AddEquiv.ofBijective f hf
  have he : ∀ x, e x = f x := fun _ => rfl
  have hes : ∀ y, f (e.symm y) = y := fun y => by rw [← he, AddEquiv.apply_symm_apply]
  have hse : ∀ x, e.symm (f x) = x := fun x => by rw [← he, AddEquiv.symm_apply_apply]
  set N : D.NMod →+ D'.NMod := D.nMap D' f hV hPi with hN
  let L' : D'.M →+ D'.NMod := N.comp (L.comp e.symm.toAddMonoidHom)
  have hL'f : ∀ x, L' (f x) = N (L x) := fun x => by
    show N (L (e.symm (f x))) = N (L x); rw [hse]
  refine ⟨L', ⟨⟨?_, ?_, ?_⟩, ?_⟩, hL'f⟩
  ·
    intro w y
    obtain ⟨x, rfl⟩ := hf.2 y
    rw [← hW, hL'f, hL'f, hL.isCartierLMap.map_smul, hN, nMap_smul D D' f hW hV hPi]
  ·
    intro y
    obtain ⟨x, rfl⟩ := hf.2 y
    rw [← hV, hL'f, hL.isCartierLMap.map_verschiebung, hN, nMap_nMk, map_zero, hPi]
  ·
    intro y
    obtain ⟨x, rfl⟩ := hf.2 y
    rw [hL'f, ← hF]
    have hl := hL.isCartierLMap.lambda_comp x
    obtain ⟨⟨m, m'⟩, hm⟩ := D.nMk_surjective (L x)
    rw [← hm, lambda_nMk] at hl
    rw [hN, ← hm, nMap_nMk, lambda_nMk, ← hPi, ← hV, ← map_add, hl]
  ·
    obtain ⟨S, instS, jS, φ, hφ, htf, Dl, hDl, g, hg, Ll, hLl, hcomp⟩ := hL.exists_lift
    have hgW := hg.1; have hgF := hg.2.1; have hgV := hg.2.2.1; have hgPi := hg.2.2.2.1; have hgpc := hg.2.2.2.2.1
    obtain ⟨γ, hγl, hγ⟩ := hg.2.2.2.2.2
    have hfg : IsBaseChangeAlong' φ Dl D' (f.comp g) := by
      refine ⟨fun w x => ?_, fun x => ?_, fun x => ?_, fun x => ?_, fun i x hx => ?_, ⟨γ, hγl, ?_⟩⟩
      · show f (g (w • x)) = _; rw [hgW, hW]; rfl
      · show f (g (Dl.frobenius x)) = _; rw [hgF, hF]; rfl
      · show f (g (Dl.verschiebung x)) = _; rw [hgV, hV]; rfl
      · show f (g (Dl.varpi x)) = _; rw [hgPi, hPi]; rfl
      · exact hpc i _ (hgpc i x hx)
      · exact isHomogeneousVBasis_of_bijective D D' f hf hW hV hpc (fun i => g (γ i)) hγ
    refine ⟨S, instS, jS, φ, hφ, htf, Dl, hDl, f.comp g, hfg, Ll, hLl, fun x => ?_⟩
    show L' (f (g x)) = _
    rw [hL'f, hcomp x, hN, nMap_nMap Dl D D' g _ _ f hV hPi]

end S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_comp_eq_nMap_comp_of_bijective
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_IsCanonicalLMap_exists_comp_eq_nMap_comp_of_bijective (solution)
