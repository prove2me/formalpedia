-- Prove2me | solution 1 for GOSNIZK.BGNCommit.soundness_order_step
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:31:54.025093+00:00
-- url     : https://prove2.me/submissions/84309bd6-c872-4ece-a132-f4dea14c976a

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

set_option autoImplicit false
open GOSNIZK.BGNCommit

theorem solution {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT]
    [Fintype GT] (S : BGNSetup G GT) (m : ZMod S.n)
    (hord : (S.e S.g S.g ^ (m * (m - 1)).val) ^ S.q = 1) :
    S.toZp m = 0 ∨ S.toZp m = 1 := by
  have ho : orderOf (S.e S.g S.g) = S.p * S.q := by
    rw [orderOf_eq_card_of_forall_mem_zpowers S.he, Nat.card_eq_fintype_card, S.card_GT]
  rw [← pow_mul] at hord
  have hdvd : S.p * S.q ∣ (m * (m - 1)).val * S.q := by
    rw [← ho]; exact orderOf_dvd_of_pow_eq_one hord
  have hqpos : 0 < S.q := S.hq.pos
  have hp : S.p ∣ (m * (m - 1)).val := Nat.dvd_of_mul_dvd_mul_right hqpos hdvd
  have h0 : S.toZp (m * (m - 1)) = 0 := by
    unfold BGNSetup.toZp
    simp only [ZMod.castHom_apply, ZMod.cast_eq_val]
    exact (ZMod.natCast_eq_zero_iff _ _).mpr hp
  rw [map_mul, map_sub, map_one] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)
