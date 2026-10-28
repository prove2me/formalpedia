-- Prove2me | solution 1 for BitDFT.serializer_fresh_routing_old_tapes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-25T06:42:37.129828+00:00
-- url     : https://prove2.me/submissions/7b7ab672-3955-4da2-8309-f75b49c5b4fe

import Definitions.Def_BitDFT_SerializerFreshTapeRouting
set_option autoImplicit false

open BitDFT.SerializerFreshTapeRouting

theorem solution (r : ℕ) (i : Fin (r+2)) (hi : 2 ≤ i.val) :
    routing r ⟨i.val+3,by have := i.isLt; omega⟩ = ⟨i.val,by omega⟩ := by
  apply (splitEquiv r).injective
  simp only [routing, Equiv.trans_apply, Equiv.apply_symm_apply]
  change Sum.map id (rotateTail r)
      (splitIndex r ⟨i.val+3,by have := i.isLt; omega⟩) =
    splitIndex r ⟨i.val,by omega⟩
  simp only [splitIndex, dif_neg (by omega : ¬ i.val+3 < 2),
    dif_neg (by omega : ¬ i.val < 2)]
  apply congrArg Sum.inr
  apply Fin.ext
  simp [rotateTail]
  rw [Fin.val_add]
  have hnum : i.val+1+r = (3+r)+(i.val-2) := by omega
  rw [hnum]
  simp [Nat.add_mod, Nat.mod_self]
  have hrem : i.val-2 < 3+r := by have := i.isLt; omega
  rw [Nat.mod_eq_of_lt hrem]
