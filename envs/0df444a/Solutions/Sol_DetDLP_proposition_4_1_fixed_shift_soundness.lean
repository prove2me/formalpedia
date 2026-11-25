-- Prove2me | solution 1 for DetDLP.proposition_4_1_fixed_shift_soundness
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T09:49:42.789824+00:00
-- url     : https://prove2.me/submissions/ac7b82af-33ed-4b42-8a3d-be698def51d0

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
  classical
  let f : G → ZMod Mlab := fun g => ((FB.tupleLabelSum Mlab y (hcover g).choose : ℤ) : ZMod Mlab)
  have hf_val : ∀ X : FB.BlockTuple,
      ((FB.tupleLabelSum Mlab y X : ℤ) : ZMod Mlab) = f (FB.tupleVal X) := by
    intro X
    let X' := (hcover (FB.tupleVal X)).choose
    have hX' : FB.tupleVal X' = FB.tupleVal X := (hcover (FB.tupleVal X)).choose_spec
    let Y := (hcover (FB.tupleVal X + P)).choose
    have hY : FB.tupleVal Y = FB.tupleVal X + P := (hcover (FB.tupleVal X + P)).choose_spec
    have h1 := hshift X Y hY
    have h2 := hshift X' Y (by rw [hY, hX'])
    push_cast at h1 h2
    have heq : ((FB.tupleLabelSum Mlab y Y : ℤ) : ZMod Mlab) -
        ((FB.tupleLabelSum Mlab y X : ℤ) : ZMod Mlab) =
      ((FB.tupleLabelSum Mlab y Y : ℤ) : ZMod Mlab) -
        ((FB.tupleLabelSum Mlab y X' : ℤ) : ZMod Mlab) := h1.trans h2.symm
    exact sub_right_inj.mp heq
  have hf_shift : ∀ g : G, f (g + P) = f g + 1 := by
    intro g
    let X := (hcover g).choose
    have hX : FB.tupleVal X = g := (hcover g).choose_spec
    let Y := (hcover (g + P)).choose
    have hY : FB.tupleVal Y = g + P := (hcover (g + P)).choose_spec
    have h1 := hshift X Y (by rw [hY, hX])
    push_cast at h1
    change ((FB.tupleLabelSum Mlab y Y : ℤ) : ZMod Mlab) =
      ((FB.tupleLabelSum Mlab y X : ℤ) : ZMod Mlab) + 1
    rw [add_comm]
    exact eq_add_of_sub_eq h1
  have hf_nsmul : ∀ t : ℕ, f (t • P) = f 0 + (t : ZMod Mlab) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [succ_nsmul, hf_shift, ih]
      push_cast
      ring
  have helem_gen : FB.elem P Q FB.genCoord = P := by
    unfold IndexedFactorBase.elem IndexedFactorBase.genCoord
    simp
  have hf0 : f 0 = 0 := by
    have hgen_y : y FB.genCoord = 1 := hinit.1
    have hgen_cons : y FB.genCoord = ((FB.tupleLabelSum Mlab y (U FB.genCoord) : ℤ) : ZMod Mlab) :=
      hinit.2 FB.genCoord
    rw [hf_val, hU, helem_gen] at hgen_cons
    have h1P : f P = f 0 + 1 := by
      simpa using hf_nsmul 1
    rw [hgen_y, h1P] at hgen_cons
    linear_combination -hgen_cons
  intro j
  calc
    y j = ((FB.tupleLabelSum Mlab y (U j) : ℤ) : ZMod Mlab) := hinit.2 j
    _ = f (FB.tupleVal (U j)) := hf_val (U j)
    _ = f (FB.elem P Q j) := by rw [hU j]
    _ = f ((lam j).val • P) := by rw [hlam j]
    _ = f 0 + ((lam j).val : ZMod Mlab) := hf_nsmul (lam j).val
    _ = lam j := by rw [hf0, zero_add, ZMod.natCast_zmod_val]
