-- Prove2me | solution 1 for GOSNIZK.BGNCommit.extraction
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:08:43.277851+00:00
-- url     : https://prove2.me/submissions/d7c85579-3c45-44b0-b7f6-b1aef1c0bbcb

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

set_option autoImplicit false
open GOSNIZK.BGNCommit

theorem solution {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : BGNSetup G GT) (h : G) (hkey : S.IsBindingKey h) (m r : ZMod S.n) :
    S.com h m r ^ S.q = (S.g ^ S.q) ^ m.val ∧ S.Ext (S.com h m r) = S.toZp m := by
  classical
  obtain ⟨x, hx, rfl⟩ := hkey
  have hord : orderOf S.g = S.p * S.q := by
    rw [orderOf_eq_card_of_forall_mem_zpowers S.hg, Nat.card_eq_fintype_card, S.card_G]
  have hgn : S.g ^ (S.p * S.q) = 1 := by rw [← hord]; exact pow_orderOf_eq_one _
  have hqne : S.q ≠ 0 := S.hq.ne_zero
  have hordq : orderOf (S.g ^ S.q) = S.p := by
    rw [orderOf_pow_of_dvd hqne (by rw [hord]; exact dvd_mul_left _ _), hord]
    exact Nat.mul_div_cancel _ S.hq.pos
  have hpq1 : (S.g ^ S.q) ^ S.p = 1 := by rw [← pow_mul, mul_comm, hgn]
  have h1 : S.com (S.g ^ (S.p * x.val)) m r ^ S.q = (S.g ^ S.q) ^ m.val := by
    unfold BGNSetup.com
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]
    have : S.g ^ (S.p * x.val * (r.val * S.q)) = 1 := by
      have : S.p * x.val * (r.val * S.q) = (S.p * S.q) * (x.val * r.val) := by ring
      rw [this, pow_mul, hgn, one_pow]
    rw [this, mul_one, mul_comm m.val S.q]
    exact pow_mul _ _ _
  refine ⟨h1, ?_⟩
  have hex : ∃ k : ℕ, k < S.p ∧ S.com (S.g ^ (S.p * x.val)) m r ^ S.q = (S.g ^ S.q) ^ k := by
    refine ⟨m.val % S.p, Nat.mod_lt _ S.hp.pos, ?_⟩
    rw [h1, ← pow_mod_orderOf, hordq]
  unfold BGNSetup.Ext
  rw [dif_pos hex]
  generalize hk : Nat.find hex = k
  have hspec : k < S.p ∧ S.com (S.g ^ (S.p * x.val)) m r ^ S.q = (S.g ^ S.q) ^ k := by
    rw [← hk]; exact Nat.find_spec hex
  rw [h1] at hspec
  have hmod : m.val ≡ k [MOD S.p] := by
    have := (pow_eq_pow_iff_modEq (x := S.g ^ S.q)).mp hspec.2
    rwa [hordq] at this
  unfold BGNSetup.toZp
  simp only [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmod.symm
