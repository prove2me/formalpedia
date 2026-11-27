-- Prove2me | solution 1 for GOSNIZK.BGNCommit.witness_indistinguishability
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:15:05.988619+00:00
-- url     : https://prove2.me/submissions/65916452-5fa8-4a8b-9a0f-befe75dbe1e0

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme
namespace GOSNIZK.BGNCommit

theorem _root_.solution {G GT : Type*} [CommGroup G] [Fintype G]
    [CommGroup GT] [Fintype GT] (S : BGNSetup G GT) (h : G) (x : ZMod S.n) (hkey : S.IsHidingKey h x) :
    (∀ c : G, ∃! π : G, S.e c (c * S.g⁻¹) = S.e h π) ∧
      ∀ r₀ r₁ : ZMod S.n, S.com h 0 r₀ = S.com h 1 r₁ → S.P01 h 0 r₀ = S.P01 h 1 r₁ := by
  have ho : orderOf S.g = S.n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers S.hg, Nat.card_eq_fintype_card, S.card_G]
  have hgn : S.g ^ S.n = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  obtain ⟨t, ht⟩ : ∃ t : ℕ, S.g ^ t = h := ⟨x.val, hkey.2.symm⟩
  set z := S.e S.g S.g with hz
  have hzn : orderOf z ∣ S.n := by
    apply orderOf_dvd_of_pow_eq_one
    have : z ^ S.n = S.e (S.g ^ S.n) S.g := by rw [map_pow]; rfl
    rw [this, hgn, map_one, MonoidHom.one_apply]
  have hbil : ∀ i j : ℤ, S.e (S.g ^ i) (S.g ^ j) = z ^ (i * j) := by
    intro i j
    have : S.e (S.g ^ i) = (S.e S.g) ^ i := map_zpow S.e S.g i
    rw [this]
    show (S.e S.g (S.g ^ j)) ^ i = _
    rw [map_zpow (S.e S.g), ← zpow_mul, mul_comm]
  have heq : ∀ i j : ℤ, (i : ZMod S.n) = (j : ZMod S.n) → z ^ i = z ^ j := by
    intro i j hij
    rw [zpow_eq_zpow_iff_modEq]
    exact ((ZMod.intCast_eq_intCast_iff _ _ _).1 hij).of_dvd (by exact_mod_cast hzn)
  have hv : ∀ a : ZMod S.n, ((a.val : ℤ) : ZMod S.n) = a := fun a => by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hzo : orderOf z = S.n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers S.he, Nat.card_eq_fintype_card, S.card_GT]
  have hht : h = S.g ^ x.val := hkey.2
  have hxx : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x hkey.1
  have hpow : ∀ u : G, ∃ k : ℕ, S.g ^ k = u := by
    intro u
    have := S.hg u
    rw [← mem_powers_iff_mem_zpowers] at this
    exact this
  have heh : ∀ k : ℕ, S.e h (S.g ^ k) = z ^ ((x.val : ℤ) * (k:ℤ)) := by
    intro k
    rw [hht, ← zpow_natCast S.g x.val, ← zpow_natCast S.g k, hbil]
  have huniq : ∀ π π' : G, S.e h π = S.e h π' → π = π' := by
    intro π π' hp
    obtain ⟨k, rfl⟩ := hpow π
    obtain ⟨l, rfl⟩ := hpow π'
    rw [heh, heh, zpow_eq_zpow_iff_modEq, hzo] at hp
    have h2 := (ZMod.intCast_eq_intCast_iff _ _ _).2 hp
    push_cast at h2
    simp only [ZMod.natCast_zmod_val] at h2
    have h3 : (k : ZMod S.n) = (l : ZMod S.n) := by
      linear_combination x⁻¹ * h2 - ((k : ZMod S.n) - (l : ZMod S.n)) * hxx
    rw [pow_eq_pow_iff_modEq, ho]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 h3
  have hex : ∀ y : GT, ∃ π : G, S.e h π = y := by
    intro y
    have hy := S.he y
    rw [← mem_powers_iff_mem_zpowers] at hy
    obtain ⟨a, ha⟩ := hy
    refine ⟨S.g ^ ((x⁻¹ * (a : ZMod S.n)).val), ?_⟩
    rw [heh, ← ha]
    show z ^ _ = z ^ a
    rw [← zpow_natCast z a]
    apply heq
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination (a : ZMod S.n) * hxx
  refine ⟨fun c => ?_, fun r₀ r₁ hc => ?_⟩
  · obtain ⟨π, hπ⟩ := hex (S.e c (c * S.g⁻¹))
    exact ⟨π, hπ.symm, fun y (hy : _ = _) => huniq _ _ (hy.symm.trans hπ.symm)⟩
  · have key : ∀ m r : ZMod S.n, (m = 0 ∨ m = 1) →
        S.e (S.com h m r) (S.com h m r * S.g⁻¹) = S.e h (S.P01 h m r) := by
      intro m r hm
      have hB : h ^ r.val = S.g ^ ((t : ℤ) * (r.val : ℤ)) := by
        rw [← ht, ← pow_mul, ← zpow_natCast]; push_cast; rfl
      have hcom : S.com h m r = S.g ^ ((m.val : ℤ) + (t : ℤ) * (r.val : ℤ)) := by
        unfold GOSNIZK.BGNCommit.BGNSetup.com
        rw [hB, zpow_add, zpow_natCast]
      have hcg : S.com h m r * S.g⁻¹ = S.g ^ ((m.val : ℤ) + (t : ℤ) * (r.val : ℤ) - 1) := by
        rw [hcom, zpow_sub, zpow_one]
      have hX : S.g ^ (2 * m - 1).val * h ^ r.val = S.g ^ (((2 * m - 1).val : ℤ) + (t : ℤ) * (r.val : ℤ)) := by
        rw [hB, zpow_add, zpow_natCast]
      have first : S.e (S.com h m r) (S.com h m r * S.g⁻¹) =
          z ^ (m * (m - 1)).val * S.e (h ^ r.val) (S.g ^ (2 * m - 1).val * h ^ r.val) := by
        rw [hcg, hcom, hX, hB, hbil, hbil, ← zpow_natCast z, ← zpow_add]
        apply heq
        push_cast
        simp only [ZMod.natCast_zmod_val]
        ring
      have hm0 : m * (m - 1) = 0 := by rcases hm with rfl | rfl <;> ring
      rw [first, hm0, ZMod.val_zero, pow_zero, one_mul]
      unfold GOSNIZK.BGNCommit.BGNSetup.P01
      rw [map_pow, map_pow]
      rfl
    apply huniq
    rw [← key 0 r₀ (Or.inl rfl), ← key 1 r₁ (Or.inr rfl), hc]


end GOSNIZK.BGNCommit

