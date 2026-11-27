-- Prove2me | solution 1 for GOSNIZK.BGNCommit.completeness_display
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:14:22.519933+00:00
-- url     : https://prove2.me/submissions/e0e67b73-b4d4-4d47-a82d-0b199e4b78d3

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme
namespace GOSNIZK.BGNCommit

theorem _root_.solution {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT]
    [Fintype GT] (S : BGNSetup G GT) (h : G) (hkey : S.IsBindingKey h ∨ ∃ x, S.IsHidingKey h x)
    (m r : ZMod S.n) :
    S.e (S.com h m r) (S.com h m r * S.g⁻¹) =
        S.e S.g S.g ^ (m * (m - 1)).val * S.e (h ^ r.val) (S.g ^ (2 * m - 1).val * h ^ r.val) ∧
      ((m = 0 ∨ m = 1) → S.e (S.com h m r) (S.com h m r * S.g⁻¹) = S.e h (S.P01 h m r)) := by
  have ho : orderOf S.g = S.n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers S.hg, Nat.card_eq_fintype_card, S.card_G]
  have hgn : S.g ^ S.n = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  obtain ⟨t, ht⟩ : ∃ t : ℕ, S.g ^ t = h := by
    have := S.hg h
    rw [← mem_powers_iff_mem_zpowers] at this
    exact this
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
  refine ⟨first, fun hm => ?_⟩
  have hm0 : m * (m - 1) = 0 := by rcases hm with rfl | rfl <;> ring
  rw [first, hm0, ZMod.val_zero, pow_zero, one_mul]
  unfold GOSNIZK.BGNCommit.BGNSetup.P01
  rw [map_pow, map_pow]
  rfl


end GOSNIZK.BGNCommit

