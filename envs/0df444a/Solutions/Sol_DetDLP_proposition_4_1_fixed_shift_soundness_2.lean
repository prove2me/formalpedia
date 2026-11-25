-- Prove2me | solution 2 for DetDLP.proposition_4_1_fixed_shift_soundness
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T10:14:49.331955+00:00
-- url     : https://prove2.me/submissions/48fb29af-10dd-4f2c-954a-420507d4f376

import Mathlib
import Definitions.Def_DetDLP_FilterAndCoset

set_option autoImplicit false

open DetDLP

theorem solution
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (Mlab : ℕ) [NeZero Mlab] (hM : 2 ≤ Mlab) (hcard : Fintype.card G = Mlab)
    (P Q : G) (hgen : addOrderOf P = Mlab)
    {m : ℕ} (FB : IndexedFactorBase G m)
    (hcover : ∀ g : G, ∃ X : FB.BlockTuple, FB.tupleVal X = g)
    (U : Fin FB.totalCoords → FB.BlockTuple)
    (hU : ∀ j : Fin FB.totalCoords, FB.tupleVal (U j) = FB.elem P Q j)
    (lam : Fin FB.totalCoords → ZMod Mlab)
    (hlam : ∀ j : Fin FB.totalCoords, (lam j).val • P = FB.elem P Q j)
    (y : Fin FB.totalCoords → ZMod Mlab)
    (hinit : FB.SatisfiesInitialCongruences Mlab U y)
    (hshift : ∀ X Y : FB.BlockTuple,
      FB.tupleVal Y = FB.tupleVal X + P →
      ((FB.tupleLabelSum Mlab y Y - FB.tupleLabelSum Mlab y X : ℤ) : ZMod Mlab) = 1) :
    ∀ j : Fin FB.totalCoords, y j = lam j := by
  let L (X : FB.BlockTuple) : ZMod Mlab := (FB.tupleLabelSum Mlab y X : ℤ)
  have step (X Y : FB.BlockTuple) (h : FB.tupleVal Y = FB.tupleVal X + P) :
      L Y = L X + 1 := by
    have hs := hshift X Y h
    rw [Int.cast_sub] at hs
    exact (sub_eq_iff_eq_add.mp hs).trans (add_comm _ _)
  obtain ⟨O, hO⟩ := hcover 0
  have along (k : ℕ) (X : FB.BlockTuple) (hX : FB.tupleVal X = k • P) :
      L X = L O + (k : ZMod Mlab) := by
    induction k generalizing X with
    | zero =>
      obtain ⟨Y, hY⟩ := hcover P
      have h1 := step X Y (by simpa [hX] using hY)
      have h2 := step O Y (by simpa [hO] using hY)
      simpa using add_right_cancel (h1.symm.trans h2)
    | succ k ih =>
      obtain ⟨Y, hY⟩ := hcover (k • P)
      rw [step Y X (by simpa [hY, succ_nsmul] using hX), ih Y hY, Nat.cast_succ, add_assoc]
  have hgenElem : FB.elem P Q FB.genCoord = P := by
    simp [IndexedFactorBase.elem, IndexedFactorBase.genCoord]
  have hone : L (U FB.genCoord) = 1 := (hinit.2 _).symm.trans hinit.1
  have hanchor := along 1 (U FB.genCoord) (by simpa [hgenElem] using hU FB.genCoord)
  have hzero : L O = 0 := by
    rw [hone, Nat.cast_one] at hanchor
    exact add_right_cancel (show L O + 1 = 0 + 1 by simpa using hanchor.symm)
  intro j
  have hj := along (lam j).val (U j) ((hU j).trans (hlam j).symm)
  rw [hinit.2 j]
  change L (U j) = lam j
  simpa [hzero] using hj
