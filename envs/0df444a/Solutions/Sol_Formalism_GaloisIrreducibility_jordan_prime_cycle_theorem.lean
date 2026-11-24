-- Prove2me | solution 1 for Formalism.GaloisIrreducibility.jordan_prime_cycle_theorem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:11:50.611803+00:00
-- url     : https://prove2.me/submissions/4435457d-7385-47d2-9dd9-033b8bac7d64

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_JordanPrime
import Theorems.Thm_Formalism_GaloisIrreducibility_CycleCommutantPowers_comm_of_conj
import Theorems.Thm_Formalism_GaloisIrreducibility_CycleCommutantPowers_eq_zpow_on_support
import Theorems.Thm_Formalism_GaloisIrreducibility_CycleCommutantPowers_exists_agree
import Theorems.Thm_Formalism_GaloisIrreducibility_CycleCommutantPowers_sylow_adjust

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Equiv Equiv.Perm MulAction
namespace Formalism.GaloisIrreducibility
theorem _root_.solution : JordanPrime := by
  intro α _ _ G g p hp hgG hgc hgp hcard hG
  classical
  set Γ : Finset α := g.supportᶜ with hΓdef
  have hmemΓ : ∀ γ, γ ∈ Γ ↔ g γ = γ := by intro γ; simp [hΓdef]
  have hΓcard : Γ.card + p = Fintype.card α := by
    rw [hΓdef, Finset.card_compl, hgp]
    have := Finset.card_le_univ g.support
    rw [hgp] at this; omega
  have hk : 3 ≤ Γ.card := by omega

  have hmt : IsMultiplyPretransitive G α Γ.card := by
    obtain ⟨m, hm⟩ : ∃ m, Γ.card = m + 1 := ⟨Γ.card - 1, by omega⟩
    have hsn : ((g.support : Set α)ᶜ).ncard = m + 1 := by
      apply Nat.add_left_cancel
      rw [Set.ncard_add_ncard_compl, Set.ncard_coe_finset, hgp, Nat.card_eq_fintype_card]
      omega
    have hsn' : m + 2 < Nat.card α := by
      rw [Nat.card_eq_fintype_card]; have := hp.two_le; omega
    have hprim : IsPreprimitive (fixingSubgroup G ((g.support : Set α)ᶜ))
        (SubMulAction.ofFixingSubgroup G ((g.support : Set α)ᶜ)) := by
      have := Equiv.Perm.isPretransitive_of_isCycle_mem hgc hgG
      apply IsPreprimitive.of_prime_card
      convert hp
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, ← hgp]
      apply congr_arg
      ext x
      simp [SubMulAction.mem_ofFixingSubgroup_iff]
    have h1 := hG.isMultiplyPreprimitive hsn hsn' hprim
    have h2 : IsMultiplyPretransitive G α (m + 2) := IsMultiplyPreprimitive.isMultiplyPretransitive ..
    rw [hm]
    exact isMultiplyPretransitive_of_le (n := m + 2) (by omega) (by omega)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.1 (by omega : 2 < Γ.card)
  rw [hmemΓ] at ha hb hc

  have build : ∀ π : Perm α, (∀ γ, g γ = γ → g (π γ) = π γ) → π * π = 1 →
      ∃ x ∈ G, (∀ γ, g γ = γ → x γ = π γ) ∧ (∀ γ, g γ = γ → x⁻¹ γ = π γ) ∧
        ∃ e : ℤ, x * g * x⁻¹ = g ^ e := by
    intro π hπ hπ2
    have hinvOf : ∀ y : Perm α, (∀ γ, g γ = γ → y γ = π γ) → ∀ γ, g γ = γ → y⁻¹ γ = π γ := by
      intro y hy γ hγ
      rw [Perm.inv_eq_iff_eq, hy _ (hπ γ hγ), ← Perm.mul_apply, hπ2, Perm.one_apply]
    obtain ⟨x0, hx0G, hx0⟩ := CycleCommutantPowers.exists_agree G Γ hmt π
    have hx0' : ∀ γ, g γ = γ → x0 γ = π γ := fun γ hγ => hx0 γ ((hmemΓ γ).2 hγ)
    obtain ⟨f, hfG, hfΓ, e, he⟩ := CycleCommutantPowers.sylow_adjust G g p hp hgG hgc hgp x0 hx0G
      (fun γ hγ => by rw [hinvOf x0 hx0' γ hγ]; exact hπ γ hγ)
    have hfx : ∀ γ, g γ = γ → (f * x0) γ = π γ := by
      intro γ hγ
      rw [Perm.mul_apply, hx0' γ hγ, hfΓ _ (hπ γ hγ)]
    exact ⟨f * x0, G.mul_mem hfG hx0G, hfx, hinvOf _ hfx, e, he⟩
  have hswap : ∀ u v : α, g u = u → g v = v → ∀ γ, g γ = γ → g (swap u v γ) = swap u v γ := by
    intro u v hu hv γ hγ
    rw [swap_apply_def]
    split_ifs <;> assumption
  obtain ⟨x, hxG, hx, hxi, u, hu⟩ := build (swap a b) (hswap a b ha hb) (swap_mul_self a b)
  obtain ⟨y, hyG, hy, hyi, w, hw⟩ := build (swap a c) (hswap a c ha hc) (swap_mul_self a c)
  set z := x * y * x⁻¹ * y⁻¹ with hzdef
  have hzG : z ∈ G := G.mul_mem (G.mul_mem (G.mul_mem hxG hyG) (G.inv_mem hxG)) (G.inv_mem hyG)
  have hz : z * g * z⁻¹ = g := CycleCommutantPowers.comm_of_conj x y g u w hu hw
  have hzc : z * g = g * z := by
    calc z * g = z * g * z⁻¹ * z := by group
      _ = g * z := by rw [hz]
  obtain ⟨j, hj⟩ := CycleCommutantPowers.eq_zpow_on_support g z hgc hzc
  set t := swap a b * swap a c with htdef
  have h3 : IsThreeCycle t := isThreeCycle_swap_mul_swap_same hab hac hbc
  have hwt : g ^ (-j) * z = t * t := by
    ext d
    by_cases hd : g d = d
    ·
      have hzd : z d = swap a b (swap a c (swap a b (swap a c d))) := by
        have e1 := hswap a c ha hc d hd
        have e2 := hswap a b ha hb _ e1
        have e3 := hswap a c ha hc _ e2
        simp only [hzdef, Perm.mul_apply]
        rw [hyi d hd, hxi _ e1, hy _ e2, hx _ e3]
      have hzΓ : g (z d) = z d := by
        rw [hzd]
        exact hswap a b ha hb _ (hswap a c ha hc _ (hswap a b ha hb _ (hswap a c ha hc d hd)))
      rw [Perm.mul_apply, zpow_apply_eq_self_of_apply_eq_self hzΓ, hzd, htdef]
      simp only [Perm.mul_apply]
    ·
      have hda : d ≠ a := fun h => hd (h ▸ ha)
      have hdb : d ≠ b := fun h => hd (h ▸ hb)
      have hdc : d ≠ c := fun h => hd (h ▸ hc)
      rw [Perm.mul_apply, hj d hd, ← Perm.mul_apply, ← zpow_add, neg_add_cancel, zpow_zero,
        Perm.one_apply, htdef]
      simp only [Perm.mul_apply]
      rw [swap_apply_of_ne_of_ne hda hdc, swap_apply_of_ne_of_ne hda hdb,
        swap_apply_of_ne_of_ne hda hdc, swap_apply_of_ne_of_ne hda hdb]
  have htt : t * t = t⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have h := pow_orderOf_eq_one t
    rw [h3.isCycle.orderOf, h3.card_support] at h
    rw [← h, pow_three', mul_assoc]
  have hwG : g ^ (-j) * z ∈ G := G.mul_mem (G.zpow_mem hgG _) hzG
  rw [hwt, htt] at hwG
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hG h3.inv hwG
end Formalism.GaloisIrreducibility
