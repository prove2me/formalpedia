-- Prove2me | solution 1 for GOSNIZK.BGNCommit.unique_trapdoor_opening
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:52:28.626385+00:00
-- url     : https://prove2.me/submissions/6bf843db-199f-492e-a059-ef03f68bdcd7

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme
namespace GOSNIZK.BGNCommit

theorem _root_.solution {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT]
    [Fintype GT] (S : BGNSetup G GT) (h : G) (x : ZMod S.n) (hkey : S.IsHidingKey h x)
    (c : G) (m' : ZMod S.n) :
    ∃! r' : ZMod S.n, S.com h m' r' = c := by
  have ho : orderOf S.g = S.n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers S.hg, Nat.card_eq_fintype_card, S.card_G]
  have hcom : ∀ a b : ZMod S.n, S.com h a b = S.g ^ (a + x * b).val := by
    intro a b
    unfold GOSNIZK.BGNCommit.BGNSetup.com
    rw [hkey.2, ← pow_mul, ← pow_add, pow_eq_pow_iff_modEq, ho, ← ZMod.natCast_eq_natCast_iff]
    push_cast
    simp only [ZMod.natCast_zmod_val]
  have hx : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x hkey.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, S.g ^ k = c := by
    have := S.hg c
    rw [← mem_powers_iff_mem_zpowers] at this
    exact this
  have hinj : ∀ a b : ZMod S.n, S.g ^ a.val = S.g ^ b.val → a = b := by
    intro a b hab
    rw [pow_eq_pow_iff_modEq, ho, ← ZMod.natCast_eq_natCast_iff] at hab
    simpa only [ZMod.natCast_zmod_val] using hab
  have hkc : c = S.g ^ (k : ZMod S.n).val := by
    rw [← hk, pow_eq_pow_iff_modEq, ho, ← ZMod.natCast_eq_natCast_iff]
    simp only [ZMod.natCast_zmod_val]
  refine ⟨((k : ZMod S.n) - m') * x⁻¹, ?_, ?_⟩
  · simp only
    rw [hcom, hkc]
    congr 2
    linear_combination ((k : ZMod S.n) - m') * hx
  · intro y hy
    rw [hcom, hkc] at hy
    have := hinj _ _ hy
    linear_combination x⁻¹ * this - y * hx


end GOSNIZK.BGNCommit

