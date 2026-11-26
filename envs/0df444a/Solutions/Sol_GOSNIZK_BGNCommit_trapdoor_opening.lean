-- Prove2me | solution 1 for GOSNIZK.BGNCommit.trapdoor_opening
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:52:27.521889+00:00
-- url     : https://prove2.me/submissions/a66e5a90-7d32-4528-b6a3-650b276c7edb

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme
namespace GOSNIZK.BGNCommit

theorem _root_.solution {G GT : Type*} [CommGroup G] [Fintype G] [CommGroup GT] [Fintype GT]
    (S : BGNSetup G GT) (h : G) (x : ZMod S.n) (hkey : S.IsHidingKey h x) (m r m' : ZMod S.n) :
    S.com h m' (S.Topen x m r m') = S.com h m r := by
  have ho : orderOf S.g = S.n := by
    rw [orderOf_eq_card_of_forall_mem_zpowers S.hg, Nat.card_eq_fintype_card, S.card_G]
  have hcom : ∀ a b : ZMod S.n, S.com h a b = S.g ^ (a + x * b).val := by
    intro a b
    unfold GOSNIZK.BGNCommit.BGNSetup.com
    rw [hkey.2, ← pow_mul, ← pow_add, pow_eq_pow_iff_modEq, ho, ← ZMod.natCast_eq_natCast_iff]
    push_cast
    simp only [ZMod.natCast_zmod_val]
  have hx : x * x⁻¹ = 1 := ZMod.mul_inv_of_unit x hkey.1
  rw [hcom, hcom]
  congr 2
  unfold GOSNIZK.BGNCommit.BGNSetup.Topen
  linear_combination (-(m' - m)) * hx


end GOSNIZK.BGNCommit

