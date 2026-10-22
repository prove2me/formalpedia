-- Prove2me | solution 1 for GOSNIZK.BGNCommit.perfect_soundness
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:11:38.756915+00:00
-- url     : https://prove2.me/submissions/2a559d1c-374c-4053-a50b-90811dba676e

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

set_option autoImplicit false
open GOSNIZK.BGNCommit

theorem solution {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : BGNSetup G GT) (h : G) (hkey : S.IsBindingKey h) (c π : G) (hv : S.V01 h c π) :
    ∃ m r : ZMod S.n, (m = 0 ∨ m = 1) ∧ c = S.com h m r := by
  classical
  have hord : orderOf S.g = S.p * S.q := by
    rw [orderOf_eq_card_of_forall_mem_zpowers S.hg, Nat.card_eq_fintype_card, S.card_G]
  have ho : orderOf (S.e S.g S.g) = S.p * S.q := by
    rw [orderOf_eq_card_of_forall_mem_zpowers S.he, Nat.card_eq_fintype_card, S.card_GT]
  have hgz : ∀ k1 k2 : ℤ, ((k1 : ZMod S.n) = (k2 : ZMod S.n)) → S.g ^ k1 = S.g ^ k2 := by
    intro k1 k2 hk
    rw [zpow_eq_zpow_iff_modEq, hord]
    exact (ZMod.intCast_eq_intCast_iff _ _ _).mp hk
  have hegz : ∀ u v : ℤ, S.e (S.g ^ u) (S.g ^ v) = (S.e S.g S.g) ^ (u * v) := by
    intro u v
    rw [map_zpow S.e S.g u]
    have : ∀ (f : G →* GT) (w : G), (f ^ u) w = (f w) ^ u := by
      intro f w
      simp
    rw [this, map_zpow, ← zpow_mul, mul_comm]
  obtain ⟨x, hx, rfl⟩ := hkey
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (S.hg c)
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (S.hg π)
  subst ha hb
  unfold BGNSetup.V01 at hv
  have hc1 : S.g ^ a * S.g⁻¹ = S.g ^ (a - 1) := by rw [zpow_sub_one]
  rw [hc1, ← zpow_natCast S.g (S.p * x.val), hegz, hegz] at hv
  have hm := zpow_eq_zpow_iff_modEq.mp hv
  rw [ho] at hm
  have hp : Fact S.p.Prime := ⟨S.hp⟩
  have hmp := Int.ModEq.of_dvd (by push_cast; exact dvd_mul_right _ _) hm
  have hz : ((a : ZMod S.p) * ((a : ZMod S.p) - 1)) = 0 := by
    have := (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmp
    push_cast at this
    rw [this]
    simp
  have key : ∀ mi : ℤ, ((a : ZMod S.p) = (mi : ZMod S.p)) →
      ∃ r : ZMod S.n, ((a : ZMod S.n)) = (mi : ZMod S.n) + (S.p : ZMod S.n) * (x.val : ZMod S.n) * r := by
    intro mi hmi
    have hdv := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hmi.symm
    obtain ⟨t, ht⟩ := hdv
    have hq : Fact S.q.Prime := ⟨S.hq⟩
    have e1 : (a : ℤ) = mi + (S.p : ℤ) * t := by linarith
    have hxy : ((x.val * (x⁻¹).val : ℕ) : ZMod S.q) = ((1 : ℤ) : ZMod S.q) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      exact ZMod.mul_inv_of_unit x hx
    obtain ⟨w, hw⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (1 : ℤ) ((x.val * (x⁻¹).val : ℕ) : ℤ) S.q).mp
      (by push_cast at hxy ⊢; exact hxy.symm)
    refine ⟨(((t * (x⁻¹).val : ℤ)) : ZMod S.n), ?_⟩
    have e2 : ((S.p : ℤ) * x.val * (t * (x⁻¹).val) : ℤ) = (S.p : ℤ) * t + ((S.p : ℤ) * S.q) * (t * w) := by
      push_cast at hw
      linear_combination (S.p : ℤ) * t * hw
    have h1 := congrArg (Int.cast : ℤ → ZMod S.n) e1
    have h2 := congrArg (Int.cast : ℤ → ZMod S.n) e2
    have hn0 : ((S.p : ZMod S.n) * (S.q : ZMod S.n)) = 0 := by
      have := ZMod.natCast_self S.n
      push_cast [BGNSetup.n] at this
      exact this
    push_cast at h1 h2 ⊢
    linear_combination h1 - h2 - ((t : ZMod S.n) * (w : ZMod S.n)) * hn0
  have fin : ∀ (m r : ZMod S.n), (a : ZMod S.n) = m + (S.p : ZMod S.n) * (x.val : ZMod S.n) * r →
      S.g ^ a = S.com (S.g ^ (S.p * x.val)) m r := by
    intro m r hmr
    unfold BGNSetup.com
    have := hgz a ((m.val + S.p * x.val * r.val : ℕ) : ℤ) (by rw [hmr]; push_cast; simp)
    rw [this, zpow_natCast, pow_add, pow_mul]
  rcases mul_eq_zero.mp hz with h0 | h1
  · obtain ⟨r, hr⟩ := key 0 (by simpa using h0)
    refine ⟨0, r, Or.inl rfl, fin 0 r ?_⟩
    simpa using hr
  · obtain ⟨r, hr⟩ := key 1 (by simpa [sub_eq_zero] using h1)
    refine ⟨1, r, Or.inr rfl, fin 1 r ?_⟩
    simpa using hr
