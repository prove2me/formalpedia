-- Prove2me | solution 1 for BitDFT.bval_map_not
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T02:14:55.834436+00:00
-- url     : https://prove2.me/submissions/93c39012-2257-403b-a440-85cf5cd1f478

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_BitDFT_bval

set_option autoImplicit false
noncomputable section
open BitDFT

namespace Prelude

theorem bval_snoc (l : List Bool) (b : Bool) :
    bval (l ++ [b]) = bval l + b.toNat * 2 ^ l.length := by
  induction l with
  | nil => simp [bval]
  | cons a t ih =>
    rw [List.cons_append, bval_cons, ih, bval_cons, List.length_cons, Nat.pow_succ]; ring

theorem bval_lt (l : List Bool) : bval l < 2 ^ l.length := by
  induction l with
  | nil => simp [bval]
  | cons a t ih =>
    rw [bval_cons, List.length_cons, Nat.pow_succ]
    have h : a.toNat ≤ 1 := by cases a <;> simp
    nlinarith

end Prelude

theorem solution (l : List Bool) :
    BitDFT.bval (l.map (fun b => !b)) = 2 ^ l.length - 1 - BitDFT.bval l := by
  induction l with
  | nil => simp [bval]
  | cons a t ih =>
    rw [List.map_cons, bval_cons, bval_cons, ih, List.length_cons, Nat.pow_succ]
    have ha : a.toNat ≤ 1 := by cases a <;> simp
    have hb : (!a).toNat = 1 - a.toNat := by cases a <;> simp
    have ht := Prelude.bval_lt t
    rw [hb]
    omega
