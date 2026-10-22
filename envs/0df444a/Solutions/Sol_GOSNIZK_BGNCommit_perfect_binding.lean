-- Prove2me | solution 1 for GOSNIZK.BGNCommit.perfect_binding
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:31:52.827994+00:00
-- url     : https://prove2.me/submissions/b16f8735-803a-4b26-adb8-3bd2e8f3c4b3

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

set_option autoImplicit false
open GOSNIZK.BGNCommit

theorem solution {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : BGNSetup G GT) (h : G) (hkey : S.IsBindingKey h)
    (m₁ r₁ m₂ r₂ : ZMod S.n) (hc : S.com h m₁ r₁ = S.com h m₂ r₂) :
    S.toZp m₁ = S.toZp m₂ := by
  obtain ⟨x, hx, rfl⟩ := hkey
  have hord : orderOf S.g = S.p * S.q := by
    rw [orderOf_eq_card_of_forall_mem_zpowers S.hg, Nat.card_eq_fintype_card, S.card_G]
  unfold BGNSetup.com at hc
  rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add] at hc
  have hmod := (pow_eq_pow_iff_modEq).mp hc
  rw [hord] at hmod
  have hp := Nat.ModEq.of_dvd (dvd_mul_right S.p S.q) hmod
  have h1 : (S.p * x.val) * r₁.val ≡ 0 [MOD S.p] := by
    apply (Nat.modEq_zero_iff_dvd).mpr
    exact ⟨x.val * r₁.val, by ring⟩
  have h2 : (S.p * x.val) * r₂.val ≡ 0 [MOD S.p] := by
    apply (Nat.modEq_zero_iff_dvd).mpr
    exact ⟨x.val * r₂.val, by ring⟩
  have h3 : m₁.val ≡ m₂.val [MOD S.p] := by
    have := hp
    have e1 : m₁.val + S.p * x.val * r₁.val ≡ m₁.val + 0 [MOD S.p] := Nat.ModEq.add_left _ h1
    have e2 : m₂.val + S.p * x.val * r₂.val ≡ m₂.val + 0 [MOD S.p] := Nat.ModEq.add_left _ h2
    simpa using (e1.symm.trans this).trans e2
  unfold BGNSetup.toZp
  simp only [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h3
