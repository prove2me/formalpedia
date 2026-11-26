-- Prove2me | solution 1 for GOSNIZK.BGNCommit.binding_key_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:55:04.708158+00:00
-- url     : https://prove2.me/submissions/b267c92e-8c02-47f7-a442-bb53c7d598cc

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme
namespace GOSNIZK.BGNCommit

theorem _root_.solution {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT]
    [Fintype GT] (S : BGNSetup G GT) (h : G) (hkey : S.IsBindingKey h) (c : G) :
    ∃ m r : ZMod S.n, c = S.com h m r ∧
      ∀ m' r' : ZMod S.n, c = S.com h m' r' → S.toZp m' = S.toZp m := by
  have ho : orderOf S.g = S.n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers S.hg, Nat.card_eq_fintype_card, S.card_G]
  obtain ⟨x, -, hh⟩ := hkey
  obtain ⟨k, hk⟩ : ∃ k : ℕ, S.g ^ k = c := by
    have := S.hg c
    rw [← mem_powers_iff_mem_zpowers] at this
    exact this
  refine ⟨(k : ZMod S.n), 0, ?_, ?_⟩
  · unfold GOSNIZK.BGNCommit.BGNSetup.com
    rw [ZMod.val_zero, pow_zero, mul_one, ← hk, pow_eq_pow_iff_modEq, ho, ← ZMod.natCast_eq_natCast_iff]
    simp only [ZMod.natCast_zmod_val]
  · intro m' r' h'
    unfold GOSNIZK.BGNCommit.BGNSetup.com at h'
    rw [← hk, hh, ← pow_mul, ← pow_add, pow_eq_pow_iff_modEq, ho] at h'
    have h2 := Nat.ModEq.of_dvd (dvd_mul_right S.p S.q) h'
    rw [← ZMod.natCast_eq_natCast_iff] at h2
    push_cast at h2
    rw [ZMod.natCast_self, zero_mul, zero_mul, add_zero] at h2
    have hc : ∀ a : ZMod S.n, S.toZp a = ((a.val : ℕ) : ZMod S.p) := by
      intro a
      conv_lhs => rw [← ZMod.natCast_zmod_val a]
      rw [map_natCast]
    rw [hc, hc, ZMod.val_natCast]
    rw [h2.symm]
    have : ((k % S.n : ℕ) : ZMod S.p) = (k : ZMod S.p) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact Nat.ModEq.of_dvd (dvd_mul_right S.p S.q) (Nat.mod_modEq k S.n)
    rw [this]


end GOSNIZK.BGNCommit

