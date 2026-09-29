-- Prove2me | solution 1 for CerednikDrinfeld.GradedCartierModuleData.exists_mem_eta_nMap_eq_of_nMap_eq_nMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/ec0eafe0-440f-5475-bb70-258881d86fd6

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData
import Definitions.Def_CerednikDrinfeld_GradedCartierNModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_mem_eta_nMap_eq_of_nMap_eq_nMap

set_option autoImplicit false

open CerednikDrinfeld

namespace EtaMilnorKit

open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B} (D : GradedCartierModuleData p B j)

theorem nMk_eq_nMk_iff (a b a' b' : D.M) :
    D.nMk (a, b) = D.nMk (a', b') ↔ ∃ t : D.M, D.verschiebung t = a - a' ∧ -D.varpi t = b - b' := by
  rw [nMk_apply, nMk_apply, Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  constructor
  · rintro ⟨m, hm⟩
    rw [nRelMap_apply, Prod.mk_sub_mk, Prod.ext_iff] at hm
    exact ⟨D.ofSigma m, hm.1, by have h__af := hm.2; simp at h__af; exact h__af⟩
  · rintro ⟨t, ht, ht'⟩
    refine ⟨D.toSigma t, ?_⟩
    rw [nRelMap_apply, Prod.mk_sub_mk, Prod.ext_iff]
    exact ⟨ht, by simp at ht' ⊢; exact ht'⟩

theorem nMk_eq_zero_iff (a b : D.M) :
    D.nMk (a, b) = 0 ↔ ∃ t : D.M, D.verschiebung t = a ∧ -D.varpi t = b := by
  rw [show (0 : D.NMod) = D.nMk (0, 0) from (map_zero D.nMk).symm, nMk_eq_nMk_iff]
  simp only [sub_zero]

theorem nMap_phi {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ m, f (D.verschiebung m) = D'.verschiebung (f m))
    (hP : ∀ m, f (D.varpi m) = D'.varpi (f m))
    (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (L' : D'.M →+ D'.NMod) (hL' : ∀ x : D'.M, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
    (hLL' : ∀ m, L' (f m) = D.nMap D' f hV hP (L m)) (z : D.NMod) :
    D.nMap D' f hV hP (D.phi L hL z) = D'.phi L' hL' (D.nMap D' f hV hP z) := by
  obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective z
  rw [phi_nMk, map_add, nMap_nMk, nMap_nMk, phi_nMk, hLL', map_zero]

end EtaMilnorKit

open EtaMilnorKit CerednikDrinfeld.GradedCartierModuleData

theorem solution
    (p : ℕ) [Fact p.Prime]
    {B B₀ B₁ B₀₁ : Type} [CommRing B] [CommRing B₀] [CommRing B₁] [CommRing B₀₁]
    {j : Zp2 p →+* B} {j₀ : Zp2 p →+* B₀} {j₁ : Zp2 p →+* B₁} {j₀₁ : Zp2 p →+* B₀₁}
    (D : GradedCartierModuleData p B j) (D₀ : GradedCartierModuleData p B₀ j₀)
    (D₁ : GradedCartierModuleData p B₁ j₁) (D₀₁ : GradedCartierModuleData p B₀₁ j₀₁)
    (f₀ : D.M →+ D₀.M) (f₁ : D.M →+ D₁.M) (g₀ : D₀.M →+ D₀₁.M) (g₁ : D₁.M →+ D₀₁.M)
    (hf₀V : ∀ m, f₀ (D.verschiebung m) = D₀.verschiebung (f₀ m)) (hf₀P : ∀ m, f₀ (D.varpi m) = D₀.varpi (f₀ m))
    (hf₁V : ∀ m, f₁ (D.verschiebung m) = D₁.verschiebung (f₁ m)) (hf₁P : ∀ m, f₁ (D.varpi m) = D₁.varpi (f₁ m))
    (hg₀V : ∀ m, g₀ (D₀.verschiebung m) = D₀₁.verschiebung (g₀ m)) (hg₀P : ∀ m, g₀ (D₀.varpi m) = D₀₁.varpi (g₀ m))
    (hg₁V : ∀ m, g₁ (D₁.verschiebung m) = D₀₁.verschiebung (g₁ m)) (hg₁P : ∀ m, g₁ (D₁.varpi m) = D₀₁.varpi (g₁ m))
    (hsq : ∀ m, g₀ (f₀ m) = g₁ (f₁ m))
    (hinj : ∀ m : D.M, f₀ m = 0 → f₁ m = 0 → m = 0)
    (hglue : ∀ (m₀ : D₀.M) (m₁ : D₁.M), g₀ m₀ = g₁ m₁ → ∃ m : D.M, f₀ m = m₀ ∧ f₁ m = m₁)
    (hg₀s : Function.Surjective g₀)
    (hV₀₁ : Function.Injective D₀₁.verschiebung)
    (L : D.M →+ D.NMod) (hL : D.IsCartierLMap L)
    (L₀ : D₀.M →+ D₀.NMod) (hL₀ : D₀.IsCartierLMap L₀)
    (L₁ : D₁.M →+ D₁.NMod) (hL₁ : D₁.IsCartierLMap L₁)
    (hLL₀ : ∀ m, L₀ (f₀ m) = D.nMap D₀ f₀ hf₀V hf₀P (L m))
    (hLL₁ : ∀ m, L₁ (f₁ m) = D.nMap D₁ f₁ hf₁V hf₁P (L m))
    (z₀ : D₀.NMod) (hz₀ : z₀ ∈ D₀.eta L₀ hL₀.map_verschiebung)
    (z₁ : D₁.NMod) (hz₁ : z₁ ∈ D₁.eta L₁ hL₁.map_verschiebung)
    (hcompat : D₀.nMap D₀₁ g₀ hg₀V hg₀P z₀ = D₁.nMap D₀₁ g₁ hg₁V hg₁P z₁) :
    ∃ z ∈ D.eta L hL.map_verschiebung,
      D.nMap D₀ f₀ hf₀V hf₀P z = z₀ ∧ D.nMap D₁ f₁ hf₁V hf₁P z = z₁ := by
  classical
  obtain ⟨⟨a₀, b₀⟩, rfl⟩ := D₀.nMk_surjective z₀
  obtain ⟨⟨a₁, b₁⟩, rfl⟩ := D₁.nMk_surjective z₁

  rw [nMap_nMk, nMap_nMk, nMk_eq_nMk_iff] at hcompat
  obtain ⟨t, ht, ht'⟩ := hcompat
  obtain ⟨t₀, rfl⟩ := hg₀s t

  set a₀' : D₀.M := a₀ - D₀.verschiebung t₀ with ha₀'
  set b₀' : D₀.M := b₀ + D₀.varpi t₀ with hb₀'
  have hz₀' : D₀.nMk (a₀', b₀') = D₀.nMk (a₀, b₀) := by
    rw [nMk_eq_nMk_iff]
    exact ⟨-t₀, by rw [map_neg, ha₀']; abel, by rw [map_neg, neg_neg, hb₀']; abel⟩
  have hga : g₀ a₀' = g₁ a₁ := by
    rw [ha₀', map_sub, hg₀V, ht]; abel
  have hgb : g₀ b₀' = g₁ b₁ := by
    rw [hb₀', map_add, hg₀P]
    have : g₀ b₀ - g₁ b₁ = -D₀₁.varpi (g₀ t₀) := ht'.symm
    calc g₀ b₀ + D₀₁.varpi (g₀ t₀) = (g₀ b₀ - g₁ b₁) + D₀₁.varpi (g₀ t₀) + g₁ b₁ := by abel
      _ = g₁ b₁ := by rw [this]; abel

  obtain ⟨a, hfa₀, hfa₁⟩ := hglue a₀' a₁ hga
  obtain ⟨b, hfb₀, hfb₁⟩ := hglue b₀' b₁ hgb
  refine ⟨D.nMk (a, b), ?_, ?_, ?_⟩
  ·
    rw [mem_eta_iff]
    rw [mem_eta_iff] at hz₀ hz₁
    obtain ⟨⟨c, d⟩, hcd⟩ := D.nMk_surjective (D.phi L hL.map_verschiebung (D.nMk (a, b)) - D.nMk (a, b))
    have hw₀ : D.nMap D₀ f₀ hf₀V hf₀P (D.nMk (c, d)) = 0 := by
      rw [hcd, map_sub, nMap_phi D D₀ f₀ hf₀V hf₀P L hL.map_verschiebung L₀ hL₀.map_verschiebung hLL₀,
        nMap_nMk, hfa₀, hfb₀, hz₀', hz₀, sub_self]
    have hw₁ : D.nMap D₁ f₁ hf₁V hf₁P (D.nMk (c, d)) = 0 := by
      rw [hcd, map_sub, nMap_phi D D₁ f₁ hf₁V hf₁P L hL.map_verschiebung L₁ hL₁.map_verschiebung hLL₁,
        nMap_nMk, hfa₁, hfb₁, hz₁, sub_self]
    rw [nMap_nMk, nMk_eq_zero_iff] at hw₀ hw₁
    obtain ⟨s₀, hs₀, hs₀'⟩ := hw₀
    obtain ⟨s₁, hs₁, hs₁'⟩ := hw₁
    have hgs : g₀ s₀ = g₁ s₁ := by
      apply hV₀₁
      rw [← hg₀V, ← hg₁V, hs₀, hs₁, hsq]
    obtain ⟨s, hs0, hs1⟩ := hglue s₀ s₁ hgs
    have hc : D.verschiebung s = c := by
      rw [← sub_eq_zero]
      apply hinj
      · rw [map_sub, hf₀V, hs0, hs₀, sub_self]
      · rw [map_sub, hf₁V, hs1, hs₁, sub_self]
    have hd : -D.varpi s = d := by
      rw [← sub_eq_zero]
      apply hinj
      · rw [map_sub, map_neg, hf₀P, hs0, hs₀', sub_self]
      · rw [map_sub, map_neg, hf₁P, hs1, hs₁', sub_self]
    have hw : D.nMk (c, d) = 0 := by
      rw [← hc, ← hd]; exact D.nMk_verschiebung_neg_varpi s
    rw [hw] at hcd
    exact (sub_eq_zero.mp hcd.symm)
  · rw [nMap_nMk, hfa₀, hfb₀, hz₀']
  · rw [nMap_nMk, hfa₁, hfb₁]

end S_CerednikDrinfeld_GradedCartierModuleData_exists_mem_eta_nMap_eq_of_nMap_eq_nMap
end P2MW
export P2MW.S_CerednikDrinfeld_GradedCartierModuleData_exists_mem_eta_nMap_eq_of_nMap_eq_nMap (solution)
