-- Prove2me | solution 1 for FiniteMagmaE677.no_e677_of_card_six
-- status  : ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-10-30T22:48:37.728266+00:00
-- url     : https://prove2.me/submissions/e69c0109-9220-4682-8b4e-5f59c8b78dfb

/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
import Definitions.Def_FiniteMagmaE677
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic

/-! Every `E677` magma with six elements is impossible: a case split on the cells of the table, with no idempotent hypothesis. -/

open FiniteMagmaE677

namespace E677Finite6c

/-- An operation on `Fin 6`. -/
abbrev Op := Fin 6 → Fin 6 → Fin 6

/-- The hypotheses of the case split. -/
structure H (op : Op) : Prop where
  /-- Equation 677. -/
  e : ∀ x y : Fin 6, x = op y (op x (op (op y x) y))

/-- Each row of an E677 operation is injective. -/
theorem H.inj {op : Op} (h : H op) (y : Fin 6) : Function.Injective (op y) :=
  Finite.injective_iff_surjective.mpr fun x => ⟨_, (h.e x y).symm⟩

/-- Every element of `Fin 6` is a numeral; the value `0` is the last case. -/
theorem cv0 (w : Fin 6) : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 0 := by
  revert w
  decide

/-- Every element of `Fin 6` is a numeral; the value `1` is the last case. -/
theorem cv1 (w : Fin 6) : w = 0 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 1 := by
  revert w
  decide

/-- Every element of `Fin 6` is a numeral; the value `2` is the last case. -/
theorem cv2 (w : Fin 6) : w = 0 ∨ w = 1 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 2 := by
  revert w
  decide

/-- Every element of `Fin 6` is a numeral; the value `3` is the last case. -/
theorem cv3 (w : Fin 6) : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 5 ∨ w = 3 := by
  revert w
  decide

/-- Every element of `Fin 6` is a numeral; the value `4` is the last case. -/
theorem cv4 (w : Fin 6) : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 5 ∨ w = 4 := by
  revert w
  decide

/-- Every element of `Fin 6` is a numeral; the value `5` is the last case. -/
theorem cv5 (w : Fin 6) : w = 0 ∨ w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 := by
  revert w
  decide

/-- The relabelling of `op` by a permutation `σ`. -/
def conj (op : Op) (σ : Equiv.Perm (Fin 6)) : Op := fun a b => σ (op (σ.symm a) (σ.symm b))

/-- The swap of two labels. -/
abbrev sw (a b : Fin 6) : Equiv.Perm (Fin 6) := Equiv.swap a b

/-- A relabelling keeps the hypotheses. -/
theorem H.cj {op : Op} (h : H op) (σ : Equiv.Perm (Fin 6)) : H (conj op σ) where
  e x y := by
    simp only [conj, Equiv.symm_apply_apply]
    rw [← h.e (σ.symm x) (σ.symm y), Equiv.apply_symm_apply]

/-- A cell of a relabelled operation. -/
theorem cc {op : Op} {σ : Equiv.Perm (Fin 6)} {a b w : Fin 6} (hab : op a b = w)
    {a' b' w' : Fin 6} (ha : σ a = a' := by decide) (hb : σ b = b' := by decide)
    (hw : σ w = w' := by decide) : conj op σ a' b' = w' := by
  subst ha hb hw
  simp only [conj, Equiv.symm_apply_apply, hab]

/-- Rule R1: equation 677 at `x y` with `op y x = a`, `op a y = b`, `op x b = c`. -/
theorem r1 {op : Op} (h : H op) {x y a b c : Fin 6} (h1 : op y x = a) (h2 : op a y = b)
    (h3 : op x b = c) : op y c = x := by
  subst h1 h2 h3
  exact (h.e x y).symm

/-- Rule R1 with a different value in the cell `op y c`. -/
theorem k1 {op : Op} (h : H op) {x y a b c d : Fin 6} (h1 : op y x = a)
    (h2 : op a y = b) (h3 : op x b = c) (h4 : op y c = d) (hne : x ≠ d := by decide) : False :=
  hne ((r1 h h1 h2 h3).symm.trans h4)

/-- Rule R3: equation 677 at `x y` and the injectivity of row `y` give the cell `op x b`. -/
theorem r3 {op : Op} (h : H op) {x y a b c : Fin 6} (h1 : op y x = a) (h2 : op a y = b)
    (h3 : op y c = x) : op x b = c := by
  apply h.inj y
  rw [h3]
  subst h1 h2
  exact (h.e x y).symm

/-- Rule R4: equation 677 at `x y` and the injectivity of rows `y`, `x` give the cell
`op a y`. -/
theorem r4 {op : Op} (h : H op) {x y a b c : Fin 6} (h1 : op y x = a) (h3 : op y c = x)
    (h4 : op x b = c) : op a y = b := by
  apply h.inj x
  rw [h4]
  apply h.inj y
  rw [h3]
  subst h1
  exact (h.e x y).symm

/-- Two cells of one row with the same value. -/
theorem kr {op : Op} (h : H op) {y a b v : Fin 6} (e1 : op y a = v) (e2 : op y b = v)
    (hab : a ≠ b := by decide) : False :=
  hab (h.inj y (e1.trans e2.symm))

/-- Rule RC: the last open cell `op y c` of a row whose other values are known has the
value `0`. -/
theorem rc0 {op : Op} (h : H op) {y : Fin 6} (c : Fin 6) {j1 j2 j3 j4 j5 : Fin 6} (e1 : op y j1 = 1)
    (e2 : op y j2 = 2) (e3 : op y j3 = 3) (e4 : op y j4 = 4) (e5 : op y j5 = 5) (hc : c ≠ j1 ∧ c ≠
    j2 ∧ c ≠ j3 ∧ c ≠ j4 ∧ c ≠ j5 := by decide) : op y c = 0 := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := hc
  rcases cv5 (op y c) with e | e | e | e | e | e
  · exact e
  · exact absurd (h.inj y (e.trans e1.symm)) n1
  · exact absurd (h.inj y (e.trans e2.symm)) n2
  · exact absurd (h.inj y (e.trans e3.symm)) n3
  · exact absurd (h.inj y (e.trans e4.symm)) n4
  · exact absurd (h.inj y (e.trans e5.symm)) n5

/-- Rule RC: the last open cell `op y c` of a row whose other values are known has the
value `1`. -/
theorem rc1 {op : Op} (h : H op) {y : Fin 6} (c : Fin 6) {j0 j2 j3 j4 j5 : Fin 6} (e0 : op y j0 = 0)
    (e2 : op y j2 = 2) (e3 : op y j3 = 3) (e4 : op y j4 = 4) (e5 : op y j5 = 5) (hc : c ≠ j0 ∧ c ≠
    j2 ∧ c ≠ j3 ∧ c ≠ j4 ∧ c ≠ j5 := by decide) : op y c = 1 := by
  obtain ⟨n0, n2, n3, n4, n5⟩ := hc
  rcases cv5 (op y c) with e | e | e | e | e | e
  · exact absurd (h.inj y (e.trans e0.symm)) n0
  · exact e
  · exact absurd (h.inj y (e.trans e2.symm)) n2
  · exact absurd (h.inj y (e.trans e3.symm)) n3
  · exact absurd (h.inj y (e.trans e4.symm)) n4
  · exact absurd (h.inj y (e.trans e5.symm)) n5

/-- Rule RC: the last open cell `op y c` of a row whose other values are known has the
value `2`. -/
theorem rc2 {op : Op} (h : H op) {y : Fin 6} (c : Fin 6) {j0 j1 j3 j4 j5 : Fin 6} (e0 : op y j0 = 0)
    (e1 : op y j1 = 1) (e3 : op y j3 = 3) (e4 : op y j4 = 4) (e5 : op y j5 = 5) (hc : c ≠ j0 ∧ c ≠
    j1 ∧ c ≠ j3 ∧ c ≠ j4 ∧ c ≠ j5 := by decide) : op y c = 2 := by
  obtain ⟨n0, n1, n3, n4, n5⟩ := hc
  rcases cv5 (op y c) with e | e | e | e | e | e
  · exact absurd (h.inj y (e.trans e0.symm)) n0
  · exact absurd (h.inj y (e.trans e1.symm)) n1
  · exact e
  · exact absurd (h.inj y (e.trans e3.symm)) n3
  · exact absurd (h.inj y (e.trans e4.symm)) n4
  · exact absurd (h.inj y (e.trans e5.symm)) n5

/-- Rule RC: the last open cell `op y c` of a row whose other values are known has the
value `3`. -/
theorem rc3 {op : Op} (h : H op) {y : Fin 6} (c : Fin 6) {j0 j1 j2 j4 j5 : Fin 6} (e0 : op y j0 = 0)
    (e1 : op y j1 = 1) (e2 : op y j2 = 2) (e4 : op y j4 = 4) (e5 : op y j5 = 5) (hc : c ≠ j0 ∧ c ≠
    j1 ∧ c ≠ j2 ∧ c ≠ j4 ∧ c ≠ j5 := by decide) : op y c = 3 := by
  obtain ⟨n0, n1, n2, n4, n5⟩ := hc
  rcases cv5 (op y c) with e | e | e | e | e | e
  · exact absurd (h.inj y (e.trans e0.symm)) n0
  · exact absurd (h.inj y (e.trans e1.symm)) n1
  · exact absurd (h.inj y (e.trans e2.symm)) n2
  · exact e
  · exact absurd (h.inj y (e.trans e4.symm)) n4
  · exact absurd (h.inj y (e.trans e5.symm)) n5

/-- Rule RC: the last open cell `op y c` of a row whose other values are known has the
value `4`. -/
theorem rc4 {op : Op} (h : H op) {y : Fin 6} (c : Fin 6) {j0 j1 j2 j3 j5 : Fin 6} (e0 : op y j0 = 0)
    (e1 : op y j1 = 1) (e2 : op y j2 = 2) (e3 : op y j3 = 3) (e5 : op y j5 = 5) (hc : c ≠ j0 ∧ c ≠
    j1 ∧ c ≠ j2 ∧ c ≠ j3 ∧ c ≠ j5 := by decide) : op y c = 4 := by
  obtain ⟨n0, n1, n2, n3, n5⟩ := hc
  rcases cv5 (op y c) with e | e | e | e | e | e
  · exact absurd (h.inj y (e.trans e0.symm)) n0
  · exact absurd (h.inj y (e.trans e1.symm)) n1
  · exact absurd (h.inj y (e.trans e2.symm)) n2
  · exact absurd (h.inj y (e.trans e3.symm)) n3
  · exact e
  · exact absurd (h.inj y (e.trans e5.symm)) n5

/-- Rule RC: the last open cell `op y c` of a row whose other values are known has the
value `5`. -/
theorem rc5 {op : Op} (h : H op) {y : Fin 6} (c : Fin 6) {j0 j1 j2 j3 j4 : Fin 6} (e0 : op y j0 = 0)
    (e1 : op y j1 = 1) (e2 : op y j2 = 2) (e3 : op y j3 = 3) (e4 : op y j4 = 4) (hc : c ≠ j0 ∧ c ≠
    j1 ∧ c ≠ j2 ∧ c ≠ j3 ∧ c ≠ j4 := by decide) : op y c = 5 := by
  obtain ⟨n0, n1, n2, n3, n4⟩ := hc
  rcases cv5 (op y c) with e | e | e | e | e | e
  · exact absurd (h.inj y (e.trans e0.symm)) n0
  · exact absurd (h.inj y (e.trans e1.symm)) n1
  · exact absurd (h.inj y (e.trans e2.symm)) n2
  · exact absurd (h.inj y (e.trans e3.symm)) n3
  · exact absurd (h.inj y (e.trans e4.symm)) n4
  · exact e

end E677Finite6c

namespace E677Finite6c

private theorem n1 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 1) (c02 : op 0 2 = 2) (c03 : op 0 3 = 3) (c04 : op 0 4 = 4) : False := by
  have c05 := rc5 h 5 c00 c01 c02 c03 c04
  rcases cv5 (op 1 0) with c10|c10|c10|c10|c10|c10
  · exact k1 h c01 c10 c10 c00
  · have c11 := r3 h c01 c10 c01
    exact kr h c10 c11
  · have c12 := r3 h c01 c10 c01
    rcases cv5 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c11 c10
    · exact kr h c11 c12
    · exact kr h c11 c10
    · have c31 := r4 h c11 c12 c10
      rcases cv4 (op 1 3) with c13|c13|c13|c13|c13|c13
      · have c30 := r1 h c31 c03 c13
        exact k1 h c03 c30 c31 c00
      · exact kr h c13 c12
      · exact kr h c13 c10
      · exact kr h c13 c11
      · have c35 := r1 h c31 c03 c13
        have c51 := r4 h c13 c11 c35
        have c50 := r4 h c05 c05 c51
        rcases cv0 (op 1 4) with c14|c14|c14|c14|c14|c14
        · exact kr h c14 c12
        · exact kr h c14 c10
        · exact kr h c14 c11
        · have c15 := rc0 h 5 c12 c10 c11 c14 c13
          exact k1 h c50 c15 c00 c50
        · exact kr h c14 c13
        have c15 := rc4 h 5 c14 c12 c10 c11 c13
        have c55 := r4 h c51 c50 c14
        have c41 := r3 h c14 c01 c15
        exact k1 h c15 c41 c55 c14
      have c34 := r1 h c31 c03 c13
      have c41 := r4 h c13 c11 c34
      have c40 := r4 h c04 c04 c41
      rcases cv5 (op 1 4) with c14|c14|c14|c14|c14|c14
      · exact k1 h c40 c14 c00 c40
      · exact kr h c14 c12
      · exact kr h c14 c10
      · exact kr h c14 c11
      · exact kr h c14 c13
      have c15 := rc0 h 5 c12 c10 c11 c13 c14
      have c45 := r1 h c40 c14 c05
      have c44 := r4 h c41 c40 c15
      have c54 := r4 h c44 c41 c40
      have c50 := r1 h c54 c05 c45
      exact k1 h c05 c50 c54 c00
    · have c41 := r4 h c11 c12 c10
      rcases cv3 (op 1 4) with c14|c14|c14|c14|c14|c14
      · have c40 := r1 h c41 c04 c14
        exact k1 h c04 c40 c41 c00
      · exact kr h c14 c12
      · exact kr h c14 c10
      · exact kr h c14 c11
      · have c45 := r1 h c41 c04 c14
        have c51 := r4 h c14 c11 c45
        have c50 := r4 h c05 c05 c51
        rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
        · exact kr h c13 c12
        · exact kr h c13 c10
        · have c15 := rc0 h 5 c12 c10 c13 c11 c14
          exact k1 h c50 c15 c00 c50
        · exact kr h c13 c11
        · exact kr h c13 c14
        have c15 := rc3 h 5 c13 c12 c10 c11 c14
        have c55 := r4 h c51 c50 c13
        have c31 := r3 h c13 c01 c15
        exact k1 h c15 c31 c55 c13
      have c43 := r1 h c41 c04 c14
      have c31 := r4 h c14 c11 c43
      have c30 := r4 h c03 c03 c31
      rcases cv5 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact k1 h c30 c13 c00 c30
      · exact kr h c13 c12
      · exact kr h c13 c10
      · exact kr h c13 c14
      · exact kr h c13 c11
      have c15 := rc0 h 5 c12 c10 c14 c11 c13
      have c35 := r1 h c30 c13 c05
      have c33 := r4 h c31 c30 c15
      have c53 := r4 h c33 c31 c30
      have c50 := r1 h c53 c05 c35
      exact k1 h c05 c50 c53 c00
    have c51 := r4 h c11 c12 c10
    rcases cv3 (op 1 5) with c15|c15|c15|c15|c15|c15
    · have c50 := r1 h c51 c05 c15
      exact k1 h c05 c50 c51 c00
    · exact kr h c15 c12
    · exact kr h c15 c10
    · have c54 := r1 h c51 c05 c15
      have c41 := r4 h c15 c11 c54
      have c40 := r4 h c04 c04 c41
      rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact kr h c13 c12
      · exact kr h c13 c10
      · have c14 := rc0 h 4 c12 c10 c13 c15 c11
        exact k1 h c40 c14 c00 c40
      · exact kr h c13 c15
      · exact kr h c13 c11
      have c14 := rc3 h 4 c13 c12 c10 c15 c11
      have c44 := r4 h c41 c40 c13
      have c31 := r3 h c13 c01 c14
      exact k1 h c14 c31 c44 c13
    · exact kr h c15 c11
    have c53 := r1 h c51 c05 c15
    have c31 := r4 h c15 c11 c53
    have c30 := r4 h c03 c03 c31
    rcases cv4 (op 1 3) with c13|c13|c13|c13|c13|c13
    · exact k1 h c30 c13 c00 c30
    · exact kr h c13 c12
    · exact kr h c13 c10
    · exact kr h c13 c15
    · exact kr h c13 c11
    have c14 := rc0 h 4 c12 c10 c15 c13 c11
    have c34 := r1 h c30 c13 c04
    have c33 := r4 h c31 c30 c14
    have c43 := r4 h c33 c31 c30
    have c40 := r1 h c43 c04 c34
    exact k1 h c04 c40 c43 c00
  · have c13 := r3 h c01 c10 c01
    rcases cv5 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c11 c10
    · exact kr h c11 c13
    · have c21 := r4 h c11 c13 c10
      rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c20 := r1 h c21 c02 c12
        exact k1 h c02 c20 c21 c00
      · exact kr h c12 c13
      · exact kr h c12 c11
      · exact kr h c12 c10
      · have c25 := r1 h c21 c02 c12
        have c51 := r4 h c12 c11 c25
        have c50 := r4 h c05 c05 c51
        rcases cv0 (op 1 4) with c14|c14|c14|c14|c14|c14
        · exact kr h c14 c13
        · exact kr h c14 c11
        · exact kr h c14 c10
        · have c15 := rc0 h 5 c13 c11 c10 c14 c12
          exact k1 h c50 c15 c00 c50
        · exact kr h c14 c12
        have c15 := rc4 h 5 c14 c13 c11 c10 c12
        have c55 := r4 h c51 c50 c14
        have c41 := r3 h c14 c01 c15
        exact k1 h c15 c41 c55 c14
      have c24 := r1 h c21 c02 c12
      have c41 := r4 h c12 c11 c24
      have c40 := r4 h c04 c04 c41
      rcases cv5 (op 1 4) with c14|c14|c14|c14|c14|c14
      · exact k1 h c40 c14 c00 c40
      · exact kr h c14 c13
      · exact kr h c14 c11
      · exact kr h c14 c10
      · exact kr h c14 c12
      have c15 := rc0 h 5 c13 c11 c10 c12 c14
      have c45 := r1 h c40 c14 c05
      have c44 := r4 h c41 c40 c15
      have c54 := r4 h c44 c41 c40
      have c50 := r1 h c54 c05 c45
      exact k1 h c05 c50 c54 c00
    · exact kr h c11 c10
    · have c41 := r4 h c11 c13 c10
      rcases cv2 (op 1 4) with c14|c14|c14|c14|c14|c14
      · have c40 := r1 h c41 c04 c14
        exact k1 h c04 c40 c41 c00
      · exact kr h c14 c13
      · exact kr h c14 c10
      · exact kr h c14 c11
      · have c45 := r1 h c41 c04 c14
        have c51 := r4 h c14 c11 c45
        have c50 := r4 h c05 c05 c51
        rcases cv0 (op 1 2) with c12|c12|c12|c12|c12|c12
        · exact kr h c12 c13
        · have c15 := rc0 h 5 c13 c12 c10 c11 c14
          exact k1 h c50 c15 c00 c50
        · exact kr h c12 c10
        · exact kr h c12 c11
        · exact kr h c12 c14
        have c15 := rc2 h 5 c12 c13 c10 c11 c14
        have c55 := r4 h c51 c50 c12
        have c21 := r3 h c12 c01 c15
        exact k1 h c15 c21 c55 c12
      have c42 := r1 h c41 c04 c14
      have c21 := r4 h c14 c11 c42
      have c20 := r4 h c02 c02 c21
      rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact k1 h c20 c12 c00 c20
      · exact kr h c12 c13
      · exact kr h c12 c14
      · exact kr h c12 c10
      · exact kr h c12 c11
      have c15 := rc0 h 5 c13 c14 c10 c11 c12
      have c25 := r1 h c20 c12 c05
      have c22 := r4 h c21 c20 c15
      have c52 := r4 h c22 c21 c20
      have c50 := r1 h c52 c05 c25
      exact k1 h c05 c50 c52 c00
    have c51 := r4 h c11 c13 c10
    rcases cv2 (op 1 5) with c15|c15|c15|c15|c15|c15
    · have c50 := r1 h c51 c05 c15
      exact k1 h c05 c50 c51 c00
    · exact kr h c15 c13
    · exact kr h c15 c10
    · have c54 := r1 h c51 c05 c15
      have c41 := r4 h c15 c11 c54
      have c40 := r4 h c04 c04 c41
      rcases cv0 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact kr h c12 c13
      · have c14 := rc0 h 4 c13 c12 c10 c15 c11
        exact k1 h c40 c14 c00 c40
      · exact kr h c12 c10
      · exact kr h c12 c15
      · exact kr h c12 c11
      have c14 := rc2 h 4 c12 c13 c10 c15 c11
      have c44 := r4 h c41 c40 c12
      have c21 := r3 h c12 c01 c14
      exact k1 h c14 c21 c44 c12
    · exact kr h c15 c11
    have c52 := r1 h c51 c05 c15
    have c21 := r4 h c15 c11 c52
    have c20 := r4 h c02 c02 c21
    rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
    · exact k1 h c20 c12 c00 c20
    · exact kr h c12 c13
    · exact kr h c12 c15
    · exact kr h c12 c10
    · exact kr h c12 c11
    have c14 := rc0 h 4 c13 c15 c10 c12 c11
    have c24 := r1 h c20 c12 c04
    have c22 := r4 h c21 c20 c14
    have c42 := r4 h c22 c21 c20
    have c40 := r1 h c42 c04 c24
    exact k1 h c04 c40 c42 c00
  · have c14 := r3 h c01 c10 c01
    rcases cv5 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c11 c10
    · exact kr h c11 c14
    · have c21 := r4 h c11 c14 c10
      rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c20 := r1 h c21 c02 c12
        exact k1 h c02 c20 c21 c00
      · exact kr h c12 c14
      · exact kr h c12 c11
      · exact kr h c12 c10
      · have c25 := r1 h c21 c02 c12
        have c51 := r4 h c12 c11 c25
        have c50 := r4 h c05 c05 c51
        rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
        · exact kr h c13 c14
        · exact kr h c13 c11
        · have c15 := rc0 h 5 c14 c11 c13 c10 c12
          exact k1 h c50 c15 c00 c50
        · exact kr h c13 c10
        · exact kr h c13 c12
        have c15 := rc3 h 5 c13 c14 c11 c10 c12
        have c55 := r4 h c51 c50 c13
        have c31 := r3 h c13 c01 c15
        exact k1 h c15 c31 c55 c13
      have c23 := r1 h c21 c02 c12
      have c31 := r4 h c12 c11 c23
      have c30 := r4 h c03 c03 c31
      rcases cv5 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact k1 h c30 c13 c00 c30
      · exact kr h c13 c14
      · exact kr h c13 c11
      · exact kr h c13 c12
      · exact kr h c13 c10
      have c15 := rc0 h 5 c14 c11 c12 c10 c13
      have c35 := r1 h c30 c13 c05
      have c33 := r4 h c31 c30 c15
      have c53 := r4 h c33 c31 c30
      have c50 := r1 h c53 c05 c35
      exact k1 h c05 c50 c53 c00
    · have c31 := r4 h c11 c14 c10
      rcases cv2 (op 1 3) with c13|c13|c13|c13|c13|c13
      · have c30 := r1 h c31 c03 c13
        exact k1 h c03 c30 c31 c00
      · exact kr h c13 c14
      · exact kr h c13 c11
      · exact kr h c13 c10
      · have c35 := r1 h c31 c03 c13
        have c51 := r4 h c13 c11 c35
        have c50 := r4 h c05 c05 c51
        rcases cv0 (op 1 2) with c12|c12|c12|c12|c12|c12
        · exact kr h c12 c14
        · have c15 := rc0 h 5 c14 c12 c11 c10 c13
          exact k1 h c50 c15 c00 c50
        · exact kr h c12 c11
        · exact kr h c12 c10
        · exact kr h c12 c13
        have c15 := rc2 h 5 c12 c14 c11 c10 c13
        have c55 := r4 h c51 c50 c12
        have c21 := r3 h c12 c01 c15
        exact k1 h c15 c21 c55 c12
      have c32 := r1 h c31 c03 c13
      have c21 := r4 h c13 c11 c32
      have c20 := r4 h c02 c02 c21
      rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact k1 h c20 c12 c00 c20
      · exact kr h c12 c14
      · exact kr h c12 c13
      · exact kr h c12 c11
      · exact kr h c12 c10
      have c15 := rc0 h 5 c14 c13 c11 c10 c12
      have c25 := r1 h c20 c12 c05
      have c22 := r4 h c21 c20 c15
      have c52 := r4 h c22 c21 c20
      have c50 := r1 h c52 c05 c25
      exact k1 h c05 c50 c52 c00
    · exact kr h c11 c10
    have c51 := r4 h c11 c14 c10
    rcases cv2 (op 1 5) with c15|c15|c15|c15|c15|c15
    · have c50 := r1 h c51 c05 c15
      exact k1 h c05 c50 c51 c00
    · exact kr h c15 c14
    · have c53 := r1 h c51 c05 c15
      have c31 := r4 h c15 c11 c53
      have c30 := r4 h c03 c03 c31
      rcases cv0 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact kr h c12 c14
      · have c13 := rc0 h 3 c14 c12 c15 c10 c11
        exact k1 h c30 c13 c00 c30
      · exact kr h c12 c15
      · exact kr h c12 c10
      · exact kr h c12 c11
      have c13 := rc2 h 3 c12 c14 c15 c10 c11
      have c33 := r4 h c31 c30 c12
      have c21 := r3 h c12 c01 c13
      exact k1 h c13 c21 c33 c12
    · exact kr h c15 c10
    · exact kr h c15 c11
    have c52 := r1 h c51 c05 c15
    have c21 := r4 h c15 c11 c52
    have c20 := r4 h c02 c02 c21
    rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
    · exact k1 h c20 c12 c00 c20
    · exact kr h c12 c14
    · exact kr h c12 c15
    · exact kr h c12 c10
    · exact kr h c12 c11
    have c13 := rc0 h 3 c14 c15 c12 c10 c11
    have c23 := r1 h c20 c12 c03
    have c22 := r4 h c21 c20 c13
    have c32 := r4 h c22 c21 c20
    have c30 := r1 h c32 c03 c23
    exact k1 h c03 c30 c32 c00
  have c15 := r3 h c01 c10 c01
  rcases cv4 (op 1 1) with c11|c11|c11|c11|c11|c11
  · exact k1 h c11 c01 c11 c10
  · exact kr h c11 c15
  · have c21 := r4 h c11 c15 c10
    rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c20 := r1 h c21 c02 c12
      exact k1 h c02 c20 c21 c00
    · exact kr h c12 c15
    · exact kr h c12 c11
    · have c24 := r1 h c21 c02 c12
      have c41 := r4 h c12 c11 c24
      have c40 := r4 h c04 c04 c41
      rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact kr h c13 c15
      · exact kr h c13 c11
      · have c14 := rc0 h 4 c15 c11 c13 c12 c10
        exact k1 h c40 c14 c00 c40
      · exact kr h c13 c12
      · exact kr h c13 c10
      have c14 := rc3 h 4 c13 c15 c11 c12 c10
      have c44 := r4 h c41 c40 c13
      have c31 := r3 h c13 c01 c14
      exact k1 h c14 c31 c44 c13
    · exact kr h c12 c10
    have c23 := r1 h c21 c02 c12
    have c31 := r4 h c12 c11 c23
    have c30 := r4 h c03 c03 c31
    rcases cv4 (op 1 3) with c13|c13|c13|c13|c13|c13
    · exact k1 h c30 c13 c00 c30
    · exact kr h c13 c15
    · exact kr h c13 c11
    · exact kr h c13 c12
    · exact kr h c13 c10
    have c14 := rc0 h 4 c15 c11 c12 c13 c10
    have c34 := r1 h c30 c13 c04
    have c33 := r4 h c31 c30 c14
    have c43 := r4 h c33 c31 c30
    have c40 := r1 h c43 c04 c34
    exact k1 h c04 c40 c43 c00
  · have c31 := r4 h c11 c15 c10
    rcases cv2 (op 1 3) with c13|c13|c13|c13|c13|c13
    · have c30 := r1 h c31 c03 c13
      exact k1 h c03 c30 c31 c00
    · exact kr h c13 c15
    · exact kr h c13 c11
    · have c34 := r1 h c31 c03 c13
      have c41 := r4 h c13 c11 c34
      have c40 := r4 h c04 c04 c41
      rcases cv0 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact kr h c12 c15
      · have c14 := rc0 h 4 c15 c12 c11 c13 c10
        exact k1 h c40 c14 c00 c40
      · exact kr h c12 c11
      · exact kr h c12 c13
      · exact kr h c12 c10
      have c14 := rc2 h 4 c12 c15 c11 c13 c10
      have c44 := r4 h c41 c40 c12
      have c21 := r3 h c12 c01 c14
      exact k1 h c14 c21 c44 c12
    · exact kr h c13 c10
    have c32 := r1 h c31 c03 c13
    have c21 := r4 h c13 c11 c32
    have c20 := r4 h c02 c02 c21
    rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
    · exact k1 h c20 c12 c00 c20
    · exact kr h c12 c15
    · exact kr h c12 c13
    · exact kr h c12 c11
    · exact kr h c12 c10
    have c14 := rc0 h 4 c15 c13 c11 c12 c10
    have c24 := r1 h c20 c12 c04
    have c22 := r4 h c21 c20 c14
    have c42 := r4 h c22 c21 c20
    have c40 := r1 h c42 c04 c24
    exact k1 h c04 c40 c42 c00
  · exact kr h c11 c10
  have c41 := r4 h c11 c15 c10
  rcases cv2 (op 1 4) with c14|c14|c14|c14|c14|c14
  · have c40 := r1 h c41 c04 c14
    exact k1 h c04 c40 c41 c00
  · exact kr h c14 c15
  · have c43 := r1 h c41 c04 c14
    have c31 := r4 h c14 c11 c43
    have c30 := r4 h c03 c03 c31
    rcases cv0 (op 1 2) with c12|c12|c12|c12|c12|c12
    · exact kr h c12 c15
    · have c13 := rc0 h 3 c15 c12 c14 c11 c10
      exact k1 h c30 c13 c00 c30
    · exact kr h c12 c14
    · exact kr h c12 c11
    · exact kr h c12 c10
    have c13 := rc2 h 3 c12 c15 c14 c11 c10
    have c33 := r4 h c31 c30 c12
    have c21 := r3 h c12 c01 c13
    exact k1 h c13 c21 c33 c12
  · exact kr h c14 c11
  · exact kr h c14 c10
  have c42 := r1 h c41 c04 c14
  have c21 := r4 h c14 c11 c42
  have c20 := r4 h c02 c02 c21
  rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
  · exact k1 h c20 c12 c00 c20
  · exact kr h c12 c15
  · exact kr h c12 c14
  · exact kr h c12 c11
  · exact kr h c12 c10
  have c13 := rc0 h 3 c15 c14 c12 c11 c10
  have c23 := r1 h c20 c12 c03
  have c22 := r4 h c21 c20 c13
  have c32 := r4 h c22 c21 c20
  have c30 := r1 h c32 c03 c23
  exact k1 h c03 c30 c32 c00

private theorem sym1 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 1) (c02 : op 0 2 = 2) (c03 : op 0 3 = 4) : False := by
  rcases cv5 (op 0 4) with c04|c04|c04|c04|c04|c04
  · exact kr h c04 c00
  · exact kr h c04 c01
  · exact kr h c04 c02
  · have c05 := rc5 h 5 c00 c01 c02 c04 c03
    rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
    · have c33 := r1 h c30 c03 c04
      exact kr h c30 c33
    · have c41 := r3 h c04 c30 c03
      rcases cv5 (op 4 3) with c43|c43|c43|c43|c43|c43
      · have c33 := r3 h c43 c04 c41
        exact kr h c30 c33
      · have c14 := r4 h c43 c41 c30
        have c13 := r1 h c14 c01 c41
        have c33 := r1 h c30 c13 c04
        have c10 := r1 h c13 c41 c33
        exact k1 h c01 c10 c13 c04
      · have c24 := r4 h c43 c41 c30
        rcases cv5 (op 4 0) with c40|c40|c40|c40|c40|c40
        · exact k1 h c03 c40 c30 c01
        · have c31 := r3 h c03 c40 c04
          have c12 := r3 h c31 c43 c30
          have c34 := r4 h c41 c40 c12
          have c23 := r4 h c34 c31 c40
          exact kr h c23 c24
        · exact kr h c40 c43
        · exact kr h c40 c41
        · have c34 := r3 h c03 c40 c04
          have c42 := r3 h c34 c43 c34
          exact kr h c40 c42
        have c35 := r3 h c03 c40 c04
        rcases cv5 (op 3 4) with c34|c34|c34|c34|c34|c34
        · have c44 := r3 h c34 c03 c35
          exact kr h c40 c44
        · exact kr h c34 c30
        · have c23 := r4 h c34 c35 c40
          exact kr h c23 c24
        · have c33 := r4 h c34 c35 c40
          exact k1 h c33 c03 c34 c33
        · exact kr h c34 c35
        have c53 := r4 h c34 c35 c40
        have c52 := r3 h c35 c43 c34
        have c54 := r1 h c53 c05 c35
        have c44 := r3 h c54 c35 c52
        exact kr h c43 c44
      · exact kr h c43 c41
      · have c44 := r4 h c43 c41 c30
        exact k1 h c44 c04 c43 c44
      have c54 := r4 h c43 c41 c30
      rcases cv2 (op 4 0) with c40|c40|c40|c40|c40|c40
      · exact k1 h c03 c40 c30 c01
      · have c31 := r3 h c03 c40 c04
        have c15 := r3 h c31 c43 c30
        have c34 := r4 h c41 c40 c15
        have c53 := r4 h c34 c31 c40
        exact kr h c53 c54
      · exact kr h c40 c41
      · have c34 := r3 h c03 c40 c04
        have c45 := r3 h c34 c43 c34
        exact k1 h c54 c05 c45 c54
      · exact kr h c40 c43
      have c32 := r3 h c03 c40 c04
      rcases cv2 (op 3 4) with c34|c34|c34|c34|c34|c34
      · have c44 := r3 h c34 c03 c32
        exact kr h c40 c44
      · exact kr h c34 c30
      · have c33 := r4 h c34 c32 c40
        exact k1 h c33 c03 c34 c33
      · exact kr h c34 c32
      · have c53 := r4 h c34 c32 c40
        exact kr h c53 c54
      have c25 := r3 h c32 c43 c34
      have c23 := r4 h c34 c32 c40
      have c24 := r1 h c23 c02 c32
      have c44 := r3 h c24 c32 c25
      exact kr h c43 c44
    · have c42 := r3 h c04 c30 c03
      rcases cv5 (op 4 3) with c43|c43|c43|c43|c43|c43
      · have c33 := r3 h c43 c04 c42
        exact kr h c30 c33
      · have c14 := r4 h c43 c42 c30
        rcases cv5 (op 4 0) with c40|c40|c40|c40|c40|c40
        · exact k1 h c03 c40 c30 c02
        · exact kr h c40 c43
        · have c32 := r3 h c03 c40 c04
          have c21 := r3 h c32 c43 c30
          have c34 := r4 h c42 c40 c21
          have c13 := r4 h c34 c32 c40
          exact kr h c13 c14
        · exact kr h c40 c42
        · have c34 := r3 h c03 c40 c04
          have c41 := r3 h c34 c43 c34
          exact kr h c40 c41
        have c35 := r3 h c03 c40 c04
        rcases cv5 (op 3 4) with c34|c34|c34|c34|c34|c34
        · have c44 := r3 h c34 c03 c35
          exact kr h c40 c44
        · have c13 := r4 h c34 c35 c40
          exact kr h c13 c14
        · exact kr h c34 c30
        · have c33 := r4 h c34 c35 c40
          exact k1 h c33 c03 c34 c33
        · exact kr h c34 c35
        have c53 := r4 h c34 c35 c40
        have c51 := r3 h c35 c43 c34
        have c54 := r1 h c53 c05 c35
        have c44 := r3 h c54 c35 c51
        exact kr h c43 c44
      · have c24 := r4 h c43 c42 c30
        have c23 := r1 h c24 c02 c42
        have c33 := r1 h c30 c23 c04
        have c20 := r1 h c23 c42 c33
        exact k1 h c02 c20 c23 c04
      · exact kr h c43 c42
      · have c44 := r4 h c43 c42 c30
        exact k1 h c44 c04 c43 c44
      have c54 := r4 h c43 c42 c30
      rcases cv1 (op 4 0) with c40|c40|c40|c40|c40|c40
      · exact k1 h c03 c40 c30 c02
      · have c32 := r3 h c03 c40 c04
        have c25 := r3 h c32 c43 c30
        have c34 := r4 h c42 c40 c25
        have c53 := r4 h c34 c32 c40
        exact kr h c53 c54
      · exact kr h c40 c42
      · have c34 := r3 h c03 c40 c04
        have c45 := r3 h c34 c43 c34
        exact k1 h c54 c05 c45 c54
      · exact kr h c40 c43
      have c31 := r3 h c03 c40 c04
      rcases cv1 (op 3 4) with c34|c34|c34|c34|c34|c34
      · have c44 := r3 h c34 c03 c31
        exact kr h c40 c44
      · exact kr h c34 c30
      · have c33 := r4 h c34 c31 c40
        exact k1 h c33 c03 c34 c33
      · exact kr h c34 c31
      · have c53 := r4 h c34 c31 c40
        exact kr h c53 c54
      have c15 := r3 h c31 c43 c34
      have c13 := r4 h c34 c31 c40
      have c14 := r1 h c13 c01 c31
      have c44 := r3 h c14 c31 c15
      exact kr h c43 c44
    · have c43 := r3 h c04 c30 c03
      have c34 := r4 h c43 c43 c30
      have c33 := r4 h c30 c34 c03
      exact kr h c30 c33
    · have c40 := r4 h c03 c04 c30
      have c44 := r3 h c04 c30 c03
      exact k1 h c40 c04 c03 c44
    have c45 := r3 h c04 c30 c03
    rcases cv2 (op 4 3) with c43|c43|c43|c43|c43|c43
    · have c33 := r3 h c43 c04 c45
      exact kr h c30 c33
    · have c14 := r4 h c43 c45 c30
      rcases cv2 (op 4 0) with c40|c40|c40|c40|c40|c40
      · exact k1 h c03 c40 c30 c05
      · exact kr h c40 c43
      · exact kr h c40 c45
      · have c34 := r3 h c03 c40 c04
        have c41 := r3 h c34 c43 c34
        exact kr h c40 c41
      · have c35 := r3 h c03 c40 c04
        have c51 := r3 h c35 c43 c30
        have c34 := r4 h c45 c40 c51
        have c13 := r4 h c34 c35 c40
        exact kr h c13 c14
      have c32 := r3 h c03 c40 c04
      rcases cv2 (op 3 4) with c34|c34|c34|c34|c34|c34
      · have c44 := r3 h c34 c03 c32
        exact kr h c40 c44
      · have c13 := r4 h c34 c32 c40
        exact kr h c13 c14
      · have c33 := r4 h c34 c32 c40
        exact k1 h c33 c03 c34 c33
      · exact kr h c34 c32
      · exact kr h c34 c30
      have c21 := r3 h c32 c43 c34
      have c23 := r4 h c34 c32 c40
      have c24 := r1 h c23 c02 c32
      have c44 := r3 h c24 c32 c21
      exact kr h c43 c44
    · exact kr h c43 c45
    · have c44 := r4 h c43 c45 c30
      exact k1 h c44 c04 c43 c44
    · have c54 := r4 h c43 c45 c30
      have c53 := r1 h c54 c05 c45
      have c33 := r1 h c30 c53 c04
      have c50 := r1 h c53 c45 c33
      exact k1 h c05 c50 c53 c04
    have c24 := r4 h c43 c45 c30
    rcases cv1 (op 4 0) with c40|c40|c40|c40|c40|c40
    · exact k1 h c03 c40 c30 c05
    · exact kr h c40 c43
    · exact kr h c40 c45
    · have c34 := r3 h c03 c40 c04
      have c42 := r3 h c34 c43 c34
      exact kr h c40 c42
    · have c35 := r3 h c03 c40 c04
      have c52 := r3 h c35 c43 c30
      have c34 := r4 h c45 c40 c52
      have c23 := r4 h c34 c35 c40
      exact kr h c23 c24
    have c31 := r3 h c03 c40 c04
    rcases cv1 (op 3 4) with c34|c34|c34|c34|c34|c34
    · have c44 := r3 h c34 c03 c31
      exact kr h c40 c44
    · have c23 := r4 h c34 c31 c40
      exact kr h c23 c24
    · have c33 := r4 h c34 c31 c40
      exact k1 h c33 c03 c34 c33
    · exact kr h c34 c31
    · exact kr h c34 c30
    have c12 := r3 h c31 c43 c34
    have c13 := r4 h c34 c31 c40
    have c14 := r1 h c13 c01 c31
    have c44 := r3 h c14 c31 c12
    exact kr h c43 c44
  · exact kr h c04 c03
  have c05 := rc3 h 5 c00 c01 c02 c03 c04
  rcases cv2 (op 1 0) with c10|c10|c10|c10|c10|c10
  · exact k1 h c01 c10 c10 c00
  · have c11 := r3 h c01 c10 c01
    exact kr h c10 c11
  · have c13 := r3 h c01 c10 c01
    rcases cv4 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c11 c10
    · exact kr h c11 c13
    · have c21 := r4 h c11 c13 c10
      have c32 := r3 h c13 c11 c10
      rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c20 := r1 h c21 c02 c12
        exact k1 h c02 c20 c21 c00
      · exact kr h c12 c13
      · exact kr h c12 c11
      · exact kr h c12 c10
      · have c24 := r1 h c21 c02 c12
        have c31 := r1 h c32 c03 c24
        exact k1 h c10 c31 c02 c12
      have c25 := r1 h c21 c02 c12
      have c51 := r4 h c12 c11 c25
      rcases cv0 (op 1 4) with c14|c14|c14|c14|c14|c14
      · exact kr h c14 c13
      · exact kr h c14 c11
      · exact kr h c14 c10
      · have c15 := rc0 h 5 c13 c11 c10 c14 c12
        exact k1 h c15 c01 c51 c15
      · exact kr h c14 c12
      have c15 := rc4 h 5 c14 c13 c11 c10 c12
      have c41 := r3 h c14 c01 c15
      have c55 := r3 h c15 c41 c12
      exact k1 h c55 c25 c51 c55
    · exact kr h c11 c10
    · have c51 := r4 h c11 c13 c10
      exact k1 h c51 c05 c13 c51
    have c41 := r4 h c11 c13 c10
    have c34 := r3 h c13 c11 c10
    rcases cv2 (op 3 0) with c30|c30|c30|c30|c30|c30
    · exact kr h c30 c34
    · have c31 := r1 h c30 c13 c01
      have c14 := r3 h c31 c03 c30
      exact k1 h c14 c01 c41 c10
    · have c33 := r4 h c30 c34 c03
      exact kr h c30 c33
    · have c43 := r4 h c30 c34 c03
      have c44 := r1 h c43 c34 c30
      have c33 := r1 h c34 c03 c44
      exact kr h c30 c33
    · have c40 := r4 h c03 c05 c30
      exact kr h c40 c41
    rcases cv4 (op 3 1) with c31|c31|c31|c31|c31|c31
    · exact kr h c31 c34
    · exact k1 h c10 c31 c01 c11
    · exact kr h c31 c30
    · have c14 := r1 h c10 c31 c03
      exact k1 h c14 c01 c41 c10
    · exact k1 h c10 c31 c05 c13
    have c15 := r1 h c10 c31 c04
    have c40 := r1 h c41 c04 c15
    exact k1 h c03 c40 c31 c04
  · have c14 := r3 h c01 c10 c01
    rcases cv5 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c11 c10
    · exact kr h c11 c14
    · have c21 := r4 h c11 c14 c10
      have c42 := r3 h c14 c11 c10
      rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c20 := r1 h c21 c02 c12
        exact k1 h c02 c20 c21 c00
      · exact kr h c12 c14
      · exact kr h c12 c11
      · exact kr h c12 c10
      · have c25 := r1 h c21 c02 c12
        have c41 := r1 h c42 c04 c25
        exact k1 h c10 c41 c02 c12
      have c23 := r1 h c21 c02 c12
      have c31 := r4 h c12 c11 c23
      rcases cv5 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact k1 h c13 c01 c31 c13
      · exact kr h c13 c14
      · exact kr h c13 c11
      · exact kr h c13 c12
      · exact kr h c13 c10
      have c15 := rc0 h 5 c14 c11 c12 c10 c13
      have c51 := r3 h c15 c01 c13
      have c33 := r3 h c13 c51 c12
      exact k1 h c33 c23 c31 c33
    · have c31 := r4 h c11 c14 c10
      exact k1 h c31 c03 c14 c31
    · exact kr h c11 c10
    have c51 := r4 h c11 c14 c10
    have c45 := r3 h c14 c11 c10
    rcases cv2 (op 4 0) with c40|c40|c40|c40|c40|c40
    · exact kr h c40 c45
    · have c41 := r1 h c40 c14 c01
      have c15 := r3 h c41 c04 c40
      exact k1 h c15 c01 c51 c10
    · have c50 := r4 h c04 c03 c40
      exact kr h c50 c51
    · have c44 := r4 h c40 c45 c04
      exact kr h c40 c44
    · have c54 := r4 h c40 c45 c04
      have c55 := r1 h c54 c45 c40
      have c44 := r1 h c45 c04 c55
      exact kr h c40 c44
    rcases cv5 (op 4 1) with c41|c41|c41|c41|c41|c41
    · exact kr h c41 c45
    · exact k1 h c10 c41 c01 c11
    · exact kr h c41 c40
    · exact k1 h c10 c41 c03 c14
    · have c15 := r1 h c10 c41 c04
      exact k1 h c15 c01 c51 c10
    have c13 := r1 h c10 c41 c05
    have c50 := r1 h c51 c05 c13
    exact k1 h c04 c50 c41 c05
  · have c15 := r3 h c01 c10 c01
    rcases cv3 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c11 c10
    · exact kr h c11 c15
    · have c21 := r4 h c11 c15 c10
      have c52 := r3 h c15 c11 c10
      rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c20 := r1 h c21 c02 c12
        exact k1 h c02 c20 c21 c00
      · exact kr h c12 c15
      · exact kr h c12 c11
      · have c23 := r1 h c21 c02 c12
        have c51 := r1 h c52 c05 c23
        exact k1 h c10 c51 c02 c12
      · exact kr h c12 c10
      have c24 := r1 h c21 c02 c12
      have c41 := r4 h c12 c11 c24
      rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact kr h c13 c15
      · exact kr h c13 c11
      · have c14 := rc0 h 4 c15 c11 c13 c12 c10
        exact k1 h c14 c01 c41 c14
      · exact kr h c13 c12
      · exact kr h c13 c10
      have c14 := rc3 h 4 c13 c15 c11 c12 c10
      have c31 := r3 h c13 c01 c14
      have c44 := r3 h c14 c31 c12
      exact k1 h c44 c24 c41 c44
    · have c41 := r4 h c11 c15 c10
      exact k1 h c41 c04 c15 c41
    · exact kr h c11 c10
    have c31 := r4 h c11 c15 c10
    have c53 := r3 h c15 c11 c10
    rcases cv2 (op 5 0) with c50|c50|c50|c50|c50|c50
    · exact kr h c50 c53
    · have c51 := r1 h c50 c15 c01
      have c13 := r3 h c51 c05 c50
      exact k1 h c13 c01 c31 c10
    · have c35 := r4 h c50 c53 c05
      have c33 := r3 h c53 c05 c50
      exact k1 h c35 c53 c50 c33
    · have c30 := r4 h c05 c04 c50
      exact kr h c30 c31
    · have c55 := r4 h c50 c53 c05
      exact kr h c50 c55
    rcases cv3 (op 5 1) with c51|c51|c51|c51|c51|c51
    · exact kr h c51 c53
    · exact k1 h c10 c51 c01 c11
    · exact kr h c51 c50
    · exact k1 h c10 c51 c04 c15
    · have c13 := r1 h c10 c51 c05
      exact k1 h c13 c01 c31 c10
    have c14 := r1 h c10 c51 c03
    have c30 := r1 h c31 c03 c14
    exact k1 h c05 c30 c51 c03
  have c12 := r3 h c01 c10 c01
  rcases cv4 (op 1 1) with c11|c11|c11|c11|c11|c11
  · exact k1 h c11 c01 c11 c10
  · exact kr h c11 c12
  · exact kr h c11 c10
  · have c31 := r4 h c11 c12 c10
    have c23 := r3 h c12 c11 c10
    rcases cv4 (op 2 1) with c21|c21|c21|c21|c21|c21
    · exact kr h c21 c23
    · exact k1 h c10 c21 c01 c11
    · exact k1 h c10 c21 c02 c12
    · have c14 := r1 h c10 c21 c03
      have c30 := r1 h c31 c03 c14
      have c32 := r3 h c23 c02 c21
      exact kr h c30 c32
    · have c13 := r1 h c10 c21 c05
      exact k1 h c13 c01 c31 c10
    have c15 := r1 h c10 c21 c04
    rcases cv4 (op 1 3) with c13|c13|c13|c13|c13|c13
    · exact kr h c13 c15
    · exact kr h c13 c12
    · exact kr h c13 c10
    · exact kr h c13 c11
    · have c14 := rc4 h 4 c15 c12 c10 c11 c13
      have c34 := r1 h c31 c03 c14
      have c51 := r4 h c13 c11 c34
      exact k1 h c15 c01 c51 c14
    have c14 := rc5 h 4 c15 c12 c10 c11 c13
    have c35 := r1 h c31 c03 c14
    have c51 := r3 h c15 c01 c14
    have c30 := r4 h c05 c04 c51
    exact kr h c30 c35
  · have c51 := r4 h c11 c12 c10
    have c25 := r3 h c12 c11 c10
    rcases cv3 (op 2 1) with c21|c21|c21|c21|c21|c21
    · exact kr h c21 c25
    · exact k1 h c10 c21 c01 c11
    · exact k1 h c10 c21 c02 c12
    · have c15 := r1 h c10 c21 c04
      exact k1 h c15 c01 c51 c10
    · have c13 := r1 h c10 c21 c05
      have c50 := r1 h c51 c05 c13
      have c52 := r3 h c25 c02 c21
      exact kr h c50 c52
    have c14 := r1 h c10 c21 c03
    rcases cv3 (op 1 3) with c13|c13|c13|c13|c13|c13
    · exact kr h c13 c14
    · exact kr h c13 c12
    · exact kr h c13 c10
    · have c54 := r1 h c51 c05 c13
      have c41 := r3 h c14 c01 c13
      have c50 := r4 h c04 c03 c41
      exact kr h c50 c54
    · exact kr h c13 c11
    have c15 := rc4 h 5 c14 c12 c10 c13 c11
    have c53 := r1 h c51 c05 c13
    have c41 := r3 h c14 c01 c15
    have c55 := r3 h c15 c41 c11
    exact kr h c53 c55
  have c41 := r4 h c11 c12 c10
  have c24 := r3 h c12 c11 c10
  rcases cv5 (op 2 1) with c21|c21|c21|c21|c21|c21
  · exact kr h c21 c24
  · exact k1 h c10 c21 c01 c11
  · exact k1 h c10 c21 c02 c12
  · have c14 := r1 h c10 c21 c03
    exact k1 h c14 c01 c41 c10
  · have c15 := r1 h c10 c21 c04
    have c40 := r1 h c41 c04 c15
    have c42 := r3 h c24 c02 c21
    exact kr h c40 c42
  have c13 := r1 h c10 c21 c05
  rcases cv5 (op 1 4) with c14|c14|c14|c14|c14|c14
  · exact kr h c14 c13
  · exact kr h c14 c12
  · exact kr h c14 c10
  · have c15 := rc5 h 5 c13 c12 c10 c14 c11
    have c45 := r1 h c41 c04 c15
    have c31 := r3 h c13 c01 c14
    have c44 := r3 h c14 c31 c11
    exact kr h c44 c45
  · exact kr h c14 c11
  have c15 := rc3 h 5 c13 c12 c10 c11 c14
  have c31 := r3 h c13 c01 c15
  have c55 := r3 h c15 c31 c14
  have c30 := r4 h c05 c04 c55
  exact kr h c30 c31

private theorem n2 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 1) (c02 : op 0 2 = 3) (c03 : op 0 3 = 2) (c04 : op 0 4 = 5) : False := by
  have c05 := rc4 h 5 c00 c01 c03 c02 c04
  rcases cv4 (op 2 0) with c20|c20|c20|c20|c20|c20
  · have c22 := r1 h c20 c02 c03
    exact kr h c20 c22
  · have c31 := r3 h c03 c20 c02
    rcases cv5 (op 3 2) with c32|c32|c32|c32|c32|c32
    · have c22 := r3 h c32 c03 c31
      exact kr h c20 c22
    · have c13 := r4 h c32 c31 c20
      have c12 := r1 h c13 c01 c31
      have c22 := r1 h c20 c12 c03
      have c10 := r1 h c12 c31 c22
      exact k1 h c01 c10 c12 c03
    · exact kr h c32 c31
    · have c33 := r4 h c32 c31 c20
      exact k1 h c33 c03 c32 c33
    · have c43 := r4 h c32 c31 c20
      rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
      · exact k1 h c02 c30 c20 c01
      · have c21 := r3 h c02 c30 c03
        have c14 := r3 h c21 c32 c20
        have c23 := r4 h c31 c30 c14
        have c42 := r4 h c23 c21 c30
        exact kr h c42 c43
      · exact kr h c30 c31
      · have c23 := r3 h c02 c30 c03
        have c34 := r3 h c23 c32 c23
        exact kr h c30 c34
      · exact kr h c30 c32
      have c25 := r3 h c02 c30 c03
      rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact k1 h c20 c12 c00 c20
      · have c21 := r1 h c20 c12 c01
        have c13 := r3 h c21 c02 c20
        exact k1 h c13 c01 c31 c12
      · have c23 := r1 h c20 c12 c02
        have c33 := r3 h c23 c02 c25
        exact kr h c30 c33
      · exact k1 h c20 c12 c04 c25
      · have c24 := r1 h c20 c12 c05
        exact k1 h c24 c02 c43 c20
      have c22 := r1 h c20 c12 c03
      have c10 := r1 h c12 c31 c22
      exact k1 h c01 c10 c12 c03
    have c53 := r4 h c32 c31 c20
    rcases cv4 (op 3 0) with c30|c30|c30|c30|c30|c30
    · exact k1 h c02 c30 c20 c01
    · have c21 := r3 h c02 c30 c03
      have c15 := r3 h c21 c32 c20
      have c23 := r4 h c31 c30 c15
      have c52 := r4 h c23 c21 c30
      exact kr h c52 c53
    · exact kr h c30 c31
    · have c23 := r3 h c02 c30 c03
      have c35 := r3 h c23 c32 c23
      exact kr h c30 c35
    · exact kr h c30 c32
    have c24 := r3 h c02 c30 c03
    rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
    · exact k1 h c20 c12 c00 c20
    · have c21 := r1 h c20 c12 c01
      have c13 := r3 h c21 c02 c20
      exact k1 h c13 c01 c31 c12
    · have c23 := r1 h c20 c12 c02
      have c33 := r3 h c23 c02 c24
      exact kr h c30 c33
    · have c25 := r1 h c20 c12 c04
      exact k1 h c25 c02 c53 c20
    · exact k1 h c20 c12 c05 c24
    have c22 := r1 h c20 c12 c03
    have c10 := r1 h c12 c31 c22
    exact k1 h c01 c10 c12 c03
  · have c32 := r3 h c03 c20 c02
    have c23 := r4 h c32 c32 c20
    have c22 := r4 h c20 c23 c02
    exact kr h c20 c22
  · have c30 := r4 h c02 c03 c20
    have c33 := r3 h c03 c20 c02
    exact k1 h c30 c03 c02 c33
  · have c35 := r3 h c03 c20 c02
    rcases cv4 (op 3 0) with c30|c30|c30|c30|c30|c30
    · exact k1 h c02 c30 c20 c05
    · have c21 := r3 h c02 c30 c03
      rcases cv4 (op 2 3) with c23|c23|c23|c23|c23|c23
      · have c33 := r3 h c23 c02 c21
        exact kr h c30 c33
      · have c12 := r4 h c23 c21 c30
        have c13 := r1 h c12 c01 c21
        have c33 := r1 h c30 c13 c02
        have c10 := r1 h c13 c21 c33
        exact k1 h c01 c10 c13 c02
      · have c22 := r4 h c23 c21 c30
        exact k1 h c22 c02 c23 c22
      · exact kr h c23 c21
      · exact kr h c23 c20
      have c42 := r4 h c23 c21 c30
      rcases cv3 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact k1 h c30 c13 c00 c30
      · have c31 := r1 h c30 c13 c01
        have c12 := r3 h c31 c03 c30
        exact k1 h c12 c01 c21 c13
      · have c33 := r1 h c30 c13 c02
        have c10 := r1 h c13 c21 c33
        exact k1 h c01 c10 c13 c02
      · exact k1 h c30 c13 c04 c35
      · have c34 := r1 h c30 c13 c05
        exact k1 h c34 c03 c42 c30
      have c32 := r1 h c30 c13 c03
      have c22 := r3 h c32 c03 c35
      exact kr h c20 c22
    · exact kr h c30 c35
    · have c23 := r3 h c02 c30 c03
      have c32 := r4 h c23 c23 c30
      have c22 := r3 h c32 c03 c35
      exact kr h c20 c22
    · have c25 := r3 h c02 c30 c03
      rcases cv4 (op 2 3) with c23|c23|c23|c23|c23|c23
      · have c52 := r4 h c20 c23 c02
        have c50 := r1 h c52 c25 c23
        have c32 := r1 h c35 c23 c50
        exact kr h c30 c32
      · have c12 := r4 h c23 c25 c30
        have c51 := r3 h c35 c23 c30
        have c32 := r4 h c25 c20 c51
        have c13 := r4 h c32 c35 c20
        exact kr h c12 c13
      · have c52 := r3 h c35 c23 c30
        exact k1 h c20 c52 c00 c20
      · exact kr h c23 c25
      · exact kr h c23 c20
      have c42 := r4 h c23 c25 c30
      have c54 := r3 h c35 c23 c30
      have c43 := r1 h c42 c04 c25
      have c32 := r4 h c25 c20 c54
      have c22 := r3 h c32 c43 c35
      exact kr h c20 c22
    have c24 := r3 h c02 c30 c03
    rcases cv4 (op 2 3) with c23|c23|c23|c23|c23|c23
    · have c33 := r3 h c23 c02 c24
      exact kr h c30 c33
    · have c12 := r4 h c23 c24 c30
      rcases cv4 (op 2 1) with c21|c21|c21|c21|c21|c21
      · have c10 := r1 h c12 c01 c21
        exact k1 h c10 c21 c00 c10
      · exact kr h c21 c23
      · exact k1 h c12 c01 c21 c12
      · exact kr h c21 c24
      · exact kr h c21 c20
      have c14 := r1 h c12 c01 c21
      rcases cv2 (op 2 2) with c22|c22|c22|c22|c22|c22
      · exact k1 h c22 c02 c23 c21
      · exact kr h c22 c23
      · exact kr h c22 c24
      · exact kr h c22 c21
      · exact kr h c22 c20
      have c25 := rc0 h 5 c23 c22 c24 c21 c20
      have c52 := r4 h c20 c25 c04
      have c40 := r4 h c05 c04 c52
      have c42 := r1 h c40 c24 c03
      have c10 := r3 h c21 c42 c23
      have c13 := r3 h c01 c10 c01
      rcases cv5 (op 1 1) with c11|c11|c11|c11|c11|c11
      · exact kr h c11 c12
      · exact kr h c11 c13
      · exact kr h c11 c14
      · exact kr h c11 c10
      · have c44 := r3 h c14 c21 c11
        exact k1 h c44 c14 c42 c40
      have c51 := r4 h c11 c13 c10
      exact k1 h c51 c05 c14 c52
    · have c22 := r4 h c23 c24 c30
      exact k1 h c22 c02 c23 c22
    · exact kr h c23 c24
    · exact kr h c23 c20
    have c42 := r4 h c23 c24 c30
    rcases cv2 (op 2 2) with c22|c22|c22|c22|c22|c22
    · exact k1 h c22 c02 c23 c24
    · rcases cv2 (op 2 1) with c21|c21|c21|c21|c21|c21
      · have c25 := rc2 h 5 c21 c22 c24 c23 c20
        exact k1 h c42 c04 c25 c42
      · exact kr h c21 c22
      · exact kr h c21 c24
      · exact kr h c21 c23
      · exact kr h c21 c20
      have c11 := r3 h c21 c22 c22
      have c12 := r4 h c22 c21 c22
      exact kr h c11 c12
    · exact kr h c22 c24
    · exact kr h c22 c23
    · exact kr h c22 c20
    rcases cv0 (op 2 1) with c21|c21|c21|c21|c21|c21
    · rcases cv5 (op 1 0) with c10|c10|c10|c10|c10|c10
      · exact k1 h c01 c10 c10 c00
      · have c11 := r3 h c01 c10 c01
        have c12 := r4 h c21 c21 c10
        exact k1 h c12 c01 c21 c11
      · have c11 := r1 h c10 c21 c01
        exact k1 h c11 c01 c11 c10
      · have c13 := r3 h c01 c10 c01
        have c12 := r4 h c21 c21 c13
        exact kr h c10 c12
      · have c14 := r3 h c01 c10 c01
        have c12 := r4 h c21 c21 c14
        exact kr h c10 c12
      have c15 := r3 h c01 c10 c01
      have c12 := r4 h c21 c21 c15
      exact kr h c10 c12
    · exact kr h c21 c22
    · exact kr h c21 c24
    · exact kr h c21 c23
    · exact kr h c21 c20
    have c25 := rc1 h 5 c21 c22 c24 c23 c20
    have c13 := r3 h c21 c02 c25
    have c41 := r1 h c42 c04 c25
    have c45 := r1 h c41 c24 c13
    rcases cv4 (op 4 0) with c40|c40|c40|c40|c40|c40
    · exact kr h c40 c42
    · exact kr h c40 c45
    · exact kr h c40 c41
    · have c34 := r4 h c40 c42 c03
      have c33 := r4 h c34 c30 c42
      exact kr h c33 c35
    · have c54 := r4 h c40 c42 c03
      have c50 := r4 h c04 c05 c40
      exact k1 h c54 c35 c42 c50
    have c44 := r4 h c40 c42 c03
    have c34 := r4 h c44 c40 c42
    have c54 := r3 h c05 c40 c04
    exact k1 h c35 c23 c54 c34
  have c34 := r3 h c03 c20 c02
  rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
  · exact k1 h c02 c30 c20 c04
  · have c21 := r3 h c02 c30 c03
    rcases cv5 (op 2 3) with c23|c23|c23|c23|c23|c23
    · have c33 := r3 h c23 c02 c21
      exact kr h c30 c33
    · have c12 := r4 h c23 c21 c30
      have c13 := r1 h c12 c01 c21
      have c33 := r1 h c30 c13 c02
      have c10 := r1 h c13 c21 c33
      exact k1 h c01 c10 c13 c02
    · have c22 := r4 h c23 c21 c30
      exact k1 h c22 c02 c23 c22
    · exact kr h c23 c21
    · exact kr h c23 c20
    have c52 := r4 h c23 c21 c30
    rcases cv3 (op 1 3) with c13|c13|c13|c13|c13|c13
    · exact k1 h c30 c13 c00 c30
    · have c31 := r1 h c30 c13 c01
      have c12 := r3 h c31 c03 c30
      exact k1 h c12 c01 c21 c13
    · have c33 := r1 h c30 c13 c02
      have c10 := r1 h c13 c21 c33
      exact k1 h c01 c10 c13 c02
    · have c35 := r1 h c30 c13 c04
      exact k1 h c35 c03 c52 c30
    · exact k1 h c30 c13 c05 c34
    have c32 := r1 h c30 c13 c03
    have c22 := r3 h c32 c03 c34
    exact kr h c20 c22
  · exact kr h c30 c34
  · have c23 := r3 h c02 c30 c03
    have c32 := r4 h c23 c23 c30
    have c22 := r3 h c32 c03 c34
    exact kr h c20 c22
  · have c24 := r3 h c02 c30 c03
    rcases cv5 (op 2 3) with c23|c23|c23|c23|c23|c23
    · have c42 := r4 h c20 c23 c02
      have c40 := r1 h c42 c24 c23
      have c32 := r1 h c34 c23 c40
      exact kr h c30 c32
    · have c12 := r4 h c23 c24 c30
      have c41 := r3 h c34 c23 c30
      have c32 := r4 h c24 c20 c41
      have c13 := r4 h c32 c34 c20
      exact kr h c12 c13
    · have c42 := r3 h c34 c23 c30
      exact k1 h c20 c42 c00 c20
    · exact kr h c23 c24
    · exact kr h c23 c20
    have c52 := r4 h c23 c24 c30
    have c45 := r3 h c34 c23 c30
    have c53 := r1 h c52 c05 c24
    have c32 := r4 h c24 c20 c45
    have c22 := r3 h c32 c53 c34
    exact kr h c20 c22
  have c25 := r3 h c02 c30 c03
  rcases cv5 (op 2 3) with c23|c23|c23|c23|c23|c23
  · have c33 := r3 h c23 c02 c25
    exact kr h c30 c33
  · have c12 := r4 h c23 c25 c30
    rcases cv5 (op 2 1) with c21|c21|c21|c21|c21|c21
    · have c10 := r1 h c12 c01 c21
      exact k1 h c10 c21 c00 c10
    · exact kr h c21 c23
    · exact k1 h c12 c01 c21 c12
    · exact kr h c21 c25
    · exact kr h c21 c20
    have c15 := r1 h c12 c01 c21
    rcases cv2 (op 2 2) with c22|c22|c22|c22|c22|c22
    · exact k1 h c22 c02 c23 c21
    · exact kr h c22 c23
    · exact kr h c22 c25
    · exact kr h c22 c20
    · exact kr h c22 c21
    have c24 := rc0 h 4 c23 c22 c25 c20 c21
    have c42 := r4 h c20 c24 c05
    have c50 := r4 h c04 c05 c42
    have c52 := r1 h c50 c25 c03
    have c10 := r3 h c21 c52 c23
    have c13 := r3 h c01 c10 c01
    rcases cv5 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact kr h c11 c12
    · exact kr h c11 c13
    · exact kr h c11 c15
    · exact kr h c11 c10
    · have c41 := r4 h c11 c13 c10
      exact k1 h c41 c04 c15 c42
    have c14 := rc4 h 4 c12 c13 c15 c10 c11
    have c51 := r4 h c11 c13 c10
    have c54 := r1 h c51 c05 c14
    have c55 := r1 h c54 c15 c42
    exact k1 h c15 c21 c55 c14
  · have c22 := r4 h c23 c25 c30
    exact k1 h c22 c02 c23 c22
  · exact kr h c23 c25
  · exact kr h c23 c20
  have c52 := r4 h c23 c25 c30
  rcases cv2 (op 2 2) with c22|c22|c22|c22|c22|c22
  · exact k1 h c22 c02 c23 c25
  · rcases cv2 (op 2 1) with c21|c21|c21|c21|c21|c21
    · have c24 := rc2 h 4 c21 c22 c25 c20 c23
      exact k1 h c52 c05 c24 c52
    · exact kr h c21 c22
    · exact kr h c21 c25
    · exact kr h c21 c20
    · exact kr h c21 c23
    have c11 := r3 h c21 c22 c22
    have c12 := r4 h c22 c21 c22
    exact kr h c11 c12
  · exact kr h c22 c25
  · exact kr h c22 c20
  · exact kr h c22 c23
  rcases cv0 (op 2 1) with c21|c21|c21|c21|c21|c21
  · rcases cv5 (op 1 0) with c10|c10|c10|c10|c10|c10
    · exact k1 h c01 c10 c10 c00
    · have c11 := r3 h c01 c10 c01
      have c12 := r4 h c21 c21 c10
      exact k1 h c12 c01 c21 c11
    · have c11 := r1 h c10 c21 c01
      exact k1 h c11 c01 c11 c10
    · have c13 := r3 h c01 c10 c01
      have c12 := r4 h c21 c21 c13
      exact kr h c10 c12
    · have c14 := r3 h c01 c10 c01
      have c12 := r4 h c21 c21 c14
      exact kr h c10 c12
    have c15 := r3 h c01 c10 c01
    have c12 := r4 h c21 c21 c15
    exact kr h c10 c12
  · exact kr h c21 c22
  · exact kr h c21 c25
  · exact kr h c21 c20
  · exact kr h c21 c23
  have c24 := rc1 h 4 c21 c22 c25 c20 c23
  have c42 := r4 h c20 c21 c01
  have c13 := r3 h c21 c02 c24
  have c51 := r1 h c52 c05 c24
  have c54 := r1 h c51 c25 c13
  rcases cv4 (op 5 0) with c50|c50|c50|c50|c50|c50
  · exact kr h c50 c52
  · exact kr h c50 c54
  · exact kr h c50 c51
  · have c35 := r4 h c50 c52 c03
    have c33 := r4 h c35 c30 c52
    exact kr h c33 c34
  · have c45 := r3 h c04 c50 c05
    exact k1 h c45 c54 c51 c42
  have c45 := r4 h c50 c52 c03
  have c40 := r4 h c05 c04 c50
  exact k1 h c45 c34 c52 c40

private theorem sym2 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 1) (c02 : op 0 2 = 3) (c03 : op 0 3 = 4) : False := by
  rcases cv2 (op 0 4) with c04|c04|c04|c04|c04|c04
  · exact kr h c04 c00
  · exact kr h c04 c01
  · exact kr h c04 c02
  · exact kr h c04 c03
  · have c05 := rc2 h 5 c00 c01 c02 c03 c04
    rcases cv3 (op 1 0) with c10|c10|c10|c10|c10|c10
    · exact k1 h c01 c10 c10 c00
    · have c11 := r3 h c01 c10 c01
      exact kr h c10 c11
    · have c12 := r3 h c01 c10 c01
      rcases cv4 (op 1 1) with c11|c11|c11|c11|c11|c11
      · exact k1 h c11 c01 c11 c10
      · exact kr h c11 c12
      · exact kr h c11 c10
      · have c31 := r4 h c11 c12 c10
        have c23 := r3 h c12 c11 c10
        rcases cv4 (op 2 0) with c20|c20|c20|c20|c20|c20
        · exact kr h c20 c23
        · have c21 := r1 h c20 c12 c01
          have c13 := r3 h c21 c02 c20
          exact k1 h c13 c01 c31 c10
        · have c22 := r4 h c20 c23 c02
          exact kr h c20 c22
        · have c32 := r4 h c20 c23 c02
          have c33 := r1 h c32 c23 c20
          have c22 := r1 h c23 c02 c33
          exact kr h c20 c22
        · have c30 := r4 h c02 c05 c20
          exact kr h c30 c31
        rcases cv3 (op 2 1) with c21|c21|c21|c21|c21|c21
        · exact kr h c21 c23
        · exact k1 h c10 c21 c01 c11
        · have c13 := r1 h c10 c21 c02
          exact k1 h c13 c01 c31 c10
        · exact kr h c21 c20
        · exact k1 h c10 c21 c05 c12
        have c14 := r1 h c10 c21 c03
        have c30 := r1 h c31 c03 c14
        exact k1 h c02 c30 c21 c03
      · have c51 := r4 h c11 c12 c10
        exact k1 h c51 c05 c12 c51
      have c41 := r4 h c11 c12 c10
      have c24 := r3 h c12 c11 c10
      rcases cv5 (op 1 5) with c15|c15|c15|c15|c15|c15
      · have c21 := r4 h c10 c15 c04
        have c40 := r1 h c41 c04 c15
        have c43 := r3 h c24 c02 c21
        exact kr h c40 c43
      · exact kr h c15 c12
      · exact kr h c15 c10
      · have c43 := r1 h c41 c04 c15
        have c21 := r1 h c24 c02 c43
        exact k1 h c10 c21 c04 c15
      · exact kr h c15 c11
      have c45 := r1 h c41 c04 c15
      rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact kr h c13 c12
      · exact kr h c13 c10
      · have c14 := rc0 h 4 c12 c10 c13 c11 c15
        exact k1 h c14 c01 c41 c10
      · exact kr h c13 c11
      · exact kr h c13 c15
      have c14 := rc3 h 4 c13 c12 c10 c11 c15
      have c31 := r3 h c13 c01 c14
      have c44 := r3 h c14 c31 c11
      exact kr h c44 c45
    · have c14 := r3 h c01 c10 c01
      rcases cv5 (op 1 1) with c11|c11|c11|c11|c11|c11
      · exact k1 h c11 c01 c11 c10
      · exact kr h c11 c14
      · have c21 := r4 h c11 c14 c10
        have c42 := r3 h c14 c11 c10
        rcases cv3 (op 1 3) with c13|c13|c13|c13|c13|c13
        · have c41 := r4 h c10 c13 c02
          have c20 := r1 h c21 c02 c13
          have c25 := r3 h c42 c04 c41
          exact kr h c20 c25
        · exact kr h c13 c14
        · exact kr h c13 c11
        · exact kr h c13 c10
        · have c25 := r1 h c21 c02 c13
          have c41 := r1 h c42 c04 c25
          exact k1 h c10 c41 c02 c13
        have c23 := r1 h c21 c02 c13
        rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
        · exact k1 h c12 c01 c21 c10
        · exact kr h c12 c14
        · exact kr h c12 c11
        · exact kr h c12 c13
        · exact kr h c12 c10
        have c15 := rc0 h 5 c14 c11 c13 c10 c12
        have c51 := r4 h c12 c11 c23
        exact k1 h c15 c01 c51 c13
      · have c31 := r4 h c11 c14 c10
        exact k1 h c31 c03 c14 c31
      · exact kr h c11 c10
      have c51 := r4 h c11 c14 c10
      have c45 := r3 h c14 c11 c10
      rcases cv2 (op 4 0) with c40|c40|c40|c40|c40|c40
      · exact kr h c40 c45
      · have c41 := r1 h c40 c14 c01
        have c15 := r3 h c41 c04 c40
        exact k1 h c15 c01 c51 c10
      · have c50 := r4 h c04 c03 c40
        exact kr h c50 c51
      · have c44 := r4 h c40 c45 c04
        exact kr h c40 c44
      · have c54 := r4 h c40 c45 c04
        have c55 := r1 h c54 c45 c40
        have c44 := r1 h c45 c04 c55
        exact kr h c40 c44
      rcases cv5 (op 4 1) with c41|c41|c41|c41|c41|c41
      · exact kr h c41 c45
      · exact k1 h c10 c41 c01 c11
      · exact kr h c41 c40
      · exact k1 h c10 c41 c03 c14
      · have c15 := r1 h c10 c41 c04
        exact k1 h c15 c01 c51 c10
      have c12 := r1 h c10 c41 c05
      have c50 := r1 h c51 c05 c12
      exact k1 h c04 c50 c41 c05
    · have c15 := r3 h c01 c10 c01
      rcases cv3 (op 1 1) with c11|c11|c11|c11|c11|c11
      · exact k1 h c11 c01 c11 c10
      · exact kr h c11 c15
      · have c21 := r4 h c11 c15 c10
        have c52 := r3 h c15 c11 c10
        rcases cv3 (op 5 0) with c50|c50|c50|c50|c50|c50
        · exact kr h c50 c52
        · have c51 := r1 h c50 c15 c01
          have c12 := r3 h c51 c05 c50
          exact k1 h c12 c01 c21 c10
        · have c25 := r4 h c50 c52 c05
          have c22 := r3 h c52 c05 c50
          exact k1 h c25 c52 c50 c22
        · have c20 := r4 h c05 c04 c50
          exact kr h c20 c21
        · have c55 := r4 h c50 c52 c05
          exact kr h c50 c55
        rcases cv2 (op 5 1) with c51|c51|c51|c51|c51|c51
        · exact kr h c51 c52
        · exact k1 h c10 c51 c01 c11
        · exact kr h c51 c50
        · exact k1 h c10 c51 c04 c15
        · have c12 := r1 h c10 c51 c05
          exact k1 h c12 c01 c21 c10
        have c13 := r1 h c10 c51 c02
        have c20 := r1 h c21 c02 c13
        exact k1 h c05 c20 c51 c02
      · have c41 := r4 h c11 c15 c10
        exact k1 h c41 c04 c15 c41
      · exact kr h c11 c10
      have c31 := r4 h c11 c15 c10
      have c53 := r3 h c15 c11 c10
      rcases cv4 (op 1 4) with c14|c14|c14|c14|c14|c14
      · have c51 := r4 h c10 c14 c03
        have c30 := r1 h c31 c03 c14
        have c32 := r3 h c53 c05 c51
        exact kr h c30 c32
      · exact kr h c14 c15
      · have c32 := r1 h c31 c03 c14
        have c51 := r1 h c53 c05 c32
        exact k1 h c10 c51 c03 c14
      · exact kr h c14 c11
      · exact kr h c14 c10
      have c34 := r1 h c31 c03 c14
      rcases cv0 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact kr h c12 c15
      · have c13 := rc0 h 3 c15 c12 c11 c14 c10
        exact k1 h c13 c01 c31 c10
      · exact kr h c12 c11
      · exact kr h c12 c14
      · exact kr h c12 c10
      have c13 := rc2 h 3 c12 c15 c11 c14 c10
      have c21 := r3 h c12 c01 c13
      have c33 := r3 h c13 c21 c11
      exact kr h c33 c34
    have c13 := r3 h c01 c10 c01
    rcases cv5 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c11 c10
    · exact kr h c11 c13
    · have c21 := r4 h c11 c13 c10
      exact k1 h c21 c02 c13 c21
    · exact kr h c11 c10
    · have c41 := r4 h c11 c13 c10
      have c34 := r3 h c13 c11 c10
      rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
      · exact kr h c30 c34
      · have c31 := r1 h c30 c13 c01
        have c14 := r3 h c31 c03 c30
        exact k1 h c14 c01 c41 c10
      · have c40 := r4 h c03 c02 c30
        exact kr h c40 c41
      · have c33 := r4 h c30 c34 c03
        exact kr h c30 c33
      · have c43 := r4 h c30 c34 c03
        have c44 := r1 h c43 c34 c30
        have c33 := r1 h c34 c03 c44
        exact kr h c30 c33
      rcases cv4 (op 3 1) with c31|c31|c31|c31|c31|c31
      · exact kr h c31 c34
      · exact k1 h c10 c31 c01 c11
      · exact k1 h c10 c31 c02 c13
      · have c14 := r1 h c10 c31 c03
        exact k1 h c14 c01 c41 c10
      · exact kr h c31 c30
      have c15 := r1 h c10 c31 c04
      have c40 := r1 h c41 c04 c15
      exact k1 h c03 c40 c31 c04
    have c51 := r4 h c11 c13 c10
    have c35 := r3 h c13 c11 c10
    rcases cv2 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c31 := r4 h c10 c12 c05
      have c50 := r1 h c51 c05 c12
      have c54 := r3 h c35 c03 c31
      exact kr h c50 c54
    · exact kr h c12 c13
    · exact kr h c12 c10
    · have c54 := r1 h c51 c05 c12
      have c31 := r1 h c35 c03 c54
      exact k1 h c10 c31 c05 c12
    · exact kr h c12 c11
    have c52 := r1 h c51 c05 c12
    rcases cv0 (op 1 4) with c14|c14|c14|c14|c14|c14
    · exact kr h c14 c13
    · exact kr h c14 c12
    · exact kr h c14 c10
    · have c15 := rc0 h 5 c13 c12 c10 c14 c11
      exact k1 h c15 c01 c51 c10
    · exact kr h c14 c11
    have c15 := rc4 h 5 c14 c13 c12 c10 c11
    have c41 := r3 h c14 c01 c15
    have c55 := r3 h c15 c41 c11
    exact kr h c52 c55
  have c05 := rc5 h 5 c00 c01 c04 c02 c03
  rcases cv5 (op 1 0) with c10|c10|c10|c10|c10|c10
  · exact k1 h c01 c10 c10 c00
  · have c11 := r3 h c01 c10 c01
    exact kr h c10 c11
  · have c12 := r3 h c01 c10 c01
    rcases cv3 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c11 c10
    · exact kr h c11 c12
    · exact kr h c11 c10
    · have c41 := r4 h c11 c12 c10
      exact k1 h c41 c04 c12 c41
    · have c51 := r4 h c11 c12 c10
      have c25 := r3 h c12 c11 c10
      rcases cv4 (op 1 5) with c15|c15|c15|c15|c15|c15
      · have c50 := r1 h c51 c05 c15
        exact k1 h c05 c50 c51 c00
      · exact kr h c15 c12
      · exact kr h c15 c10
      · have c53 := r1 h c51 c05 c15
        have c21 := r1 h c25 c02 c53
        exact k1 h c10 c21 c05 c15
      · exact kr h c15 c11
      have c54 := r1 h c51 c05 c15
      have c41 := r4 h c15 c11 c54
      rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact kr h c13 c12
      · exact kr h c13 c10
      · have c14 := rc0 h 4 c12 c10 c13 c15 c11
        exact k1 h c14 c01 c41 c14
      · exact kr h c13 c15
      · exact kr h c13 c11
      have c14 := rc3 h 4 c13 c12 c10 c15 c11
      have c31 := r3 h c13 c01 c14
      have c44 := r3 h c14 c31 c15
      exact k1 h c44 c54 c41 c44
    have c31 := r4 h c11 c12 c10
    have c23 := r3 h c12 c11 c10
    rcases cv5 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact kr h c20 c23
    · have c21 := r1 h c20 c12 c01
      have c13 := r3 h c21 c02 c20
      exact k1 h c13 c01 c31 c10
    · have c22 := r4 h c20 c23 c02
      exact kr h c20 c22
    · have c32 := r4 h c20 c23 c02
      have c33 := r1 h c32 c23 c20
      have c22 := r1 h c23 c02 c33
      exact kr h c20 c22
    · have c30 := r4 h c02 c04 c20
      exact kr h c30 c31
    rcases cv3 (op 2 1) with c21|c21|c21|c21|c21|c21
    · exact kr h c21 c23
    · exact k1 h c10 c21 c01 c11
    · have c13 := r1 h c10 c21 c02
      exact k1 h c13 c01 c31 c10
    · exact k1 h c10 c21 c04 c12
    · exact kr h c21 c20
    have c14 := r1 h c10 c21 c03
    have c30 := r1 h c31 c03 c14
    exact k1 h c02 c30 c21 c03
  · have c13 := r3 h c01 c10 c01
    rcases cv4 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c11 c10
    · exact kr h c11 c13
    · have c21 := r4 h c11 c13 c10
      exact k1 h c21 c02 c13 c21
    · exact kr h c11 c10
    · have c51 := r4 h c11 c13 c10
      have c35 := r3 h c13 c11 c10
      rcases cv2 (op 1 5) with c15|c15|c15|c15|c15|c15
      · have c50 := r1 h c51 c05 c15
        exact k1 h c05 c50 c51 c00
      · exact kr h c15 c13
      · exact kr h c15 c10
      · have c54 := r1 h c51 c05 c15
        have c31 := r1 h c35 c03 c54
        exact k1 h c10 c31 c05 c15
      · exact kr h c15 c11
      have c52 := r1 h c51 c05 c15
      have c21 := r4 h c15 c11 c52
      rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact k1 h c12 c01 c21 c12
      · exact kr h c12 c13
      · exact kr h c12 c15
      · exact kr h c12 c10
      · exact kr h c12 c11
      have c14 := rc0 h 4 c13 c15 c10 c12 c11
      have c41 := r3 h c14 c01 c12
      have c22 := r3 h c12 c41 c15
      exact k1 h c22 c52 c21 c22
    have c41 := r4 h c11 c13 c10
    have c34 := r3 h c13 c11 c10
    rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
    · exact kr h c30 c34
    · have c31 := r1 h c30 c13 c01
      have c14 := r3 h c31 c03 c30
      exact k1 h c14 c01 c41 c10
    · have c40 := r4 h c03 c02 c30
      exact kr h c40 c41
    · have c33 := r4 h c30 c34 c03
      exact kr h c30 c33
    · have c43 := r4 h c30 c34 c03
      have c44 := r1 h c43 c34 c30
      have c33 := r1 h c34 c03 c44
      exact kr h c30 c33
    rcases cv4 (op 3 1) with c31|c31|c31|c31|c31|c31
    · exact kr h c31 c34
    · exact k1 h c10 c31 c01 c11
    · exact k1 h c10 c31 c02 c13
    · have c14 := r1 h c10 c31 c03
      exact k1 h c14 c01 c41 c10
    · exact kr h c31 c30
    have c12 := r1 h c10 c31 c04
    have c40 := r1 h c41 c04 c12
    exact k1 h c03 c40 c31 c04
  · have c14 := r3 h c01 c10 c01
    rcases cv5 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c11 c10
    · exact kr h c11 c14
    · have c21 := r4 h c11 c14 c10
      have c42 := r3 h c14 c11 c10
      rcases cv5 (op 4 0) with c40|c40|c40|c40|c40|c40
      · exact kr h c40 c42
      · have c41 := r1 h c40 c14 c01
        have c12 := r3 h c41 c04 c40
        exact k1 h c12 c01 c21 c10
      · have c24 := r4 h c40 c42 c04
        have c22 := r3 h c42 c04 c40
        exact k1 h c24 c42 c40 c22
      · have c20 := r4 h c04 c03 c40
        exact kr h c20 c21
      · have c44 := r4 h c40 c42 c04
        exact kr h c40 c44
      rcases cv2 (op 4 1) with c41|c41|c41|c41|c41|c41
      · exact kr h c41 c42
      · exact k1 h c10 c41 c01 c11
      · exact k1 h c10 c41 c03 c14
      · have c12 := r1 h c10 c41 c04
        exact k1 h c12 c01 c21 c10
      · exact kr h c41 c40
      have c13 := r1 h c10 c41 c02
      have c20 := r1 h c21 c02 c13
      exact k1 h c04 c20 c41 c02
    · have c31 := r4 h c11 c14 c10
      exact k1 h c31 c03 c14 c31
    · exact kr h c11 c10
    have c51 := r4 h c11 c14 c10
    have c45 := r3 h c14 c11 c10
    rcases cv3 (op 1 5) with c15|c15|c15|c15|c15|c15
    · have c50 := r1 h c51 c05 c15
      exact k1 h c05 c50 c51 c00
    · exact kr h c15 c14
    · have c52 := r1 h c51 c05 c15
      have c41 := r1 h c45 c04 c52
      exact k1 h c10 c41 c05 c15
    · exact kr h c15 c10
    · exact kr h c15 c11
    have c53 := r1 h c51 c05 c15
    have c31 := r4 h c15 c11 c53
    rcases cv0 (op 1 2) with c12|c12|c12|c12|c12|c12
    · exact kr h c12 c14
    · have c13 := rc0 h 3 c14 c12 c15 c10 c11
      exact k1 h c13 c01 c31 c13
    · exact kr h c12 c15
    · exact kr h c12 c10
    · exact kr h c12 c11
    have c13 := rc2 h 3 c12 c14 c15 c10 c11
    have c21 := r3 h c12 c01 c13
    have c33 := r3 h c13 c21 c15
    exact k1 h c33 c53 c31 c33
  have c15 := r3 h c01 c10 c01
  rcases cv4 (op 1 1) with c11|c11|c11|c11|c11|c11
  · exact k1 h c11 c01 c11 c10
  · exact kr h c11 c15
  · have c21 := r4 h c11 c15 c10
    have c52 := r3 h c15 c11 c10
    rcases cv3 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact kr h c20 c21
    · have c12 := r4 h c20 c21 c01
      have c22 := r3 h c12 c11 c11
      exact k1 h c22 c12 c21 c20
    · have c22 := r4 h c20 c21 c01
      have c13 := r3 h c21 c02 c22
      exact kr h c11 c13
    · have c30 := r4 h c02 c04 c20
      have c32 := r1 h c30 c03 c04
      exact kr h c30 c32
    · exact k1 h c20 c52 c00 c20
    have c32 := r4 h c20 c21 c01
    rcases cv4 (op 1 3) with c13|c13|c13|c13|c13|c13
    · exact k1 h c21 c02 c13 c20
    · exact kr h c13 c15
    · exact kr h c13 c11
    · have c23 := r1 h c21 c02 c13
      have c31 := r1 h c32 c13 c23
      exact k1 h c13 c31 c32 c11
    · exact kr h c13 c10
    have c24 := r1 h c21 c02 c13
    have c31 := r1 h c32 c13 c24
    have c23 := r4 h c31 c32 c11
    exact kr h c23 c24
  · have c31 := r4 h c11 c15 c10
    have c53 := r3 h c15 c11 c10
    rcases cv4 (op 3 0) with c30|c30|c30|c30|c30|c30
    · exact kr h c30 c31
    · have c13 := r4 h c30 c31 c01
      have c33 := r3 h c13 c11 c11
      exact k1 h c33 c13 c31 c30
    · have c40 := r4 h c03 c02 c30
      have c43 := r1 h c40 c04 c02
      exact kr h c40 c43
    · have c33 := r4 h c30 c31 c01
      have c14 := r3 h c31 c03 c33
      exact kr h c11 c14
    · exact k1 h c30 c53 c00 c30
    have c43 := r4 h c30 c31 c01
    rcases cv2 (op 1 4) with c14|c14|c14|c14|c14|c14
    · exact k1 h c31 c03 c14 c30
    · exact kr h c14 c15
    · exact kr h c14 c11
    · have c34 := r1 h c31 c03 c14
      have c41 := r1 h c43 c14 c34
      exact k1 h c14 c41 c43 c11
    · exact kr h c14 c10
    have c32 := r1 h c31 c03 c14
    have c41 := r1 h c43 c14 c32
    have c34 := r4 h c41 c43 c11
    exact kr h c32 c34
  · exact kr h c11 c10
  have c41 := r4 h c11 c15 c10
  have c54 := r3 h c15 c11 c10
  rcases cv2 (op 4 0) with c40|c40|c40|c40|c40|c40
  · exact kr h c40 c41
  · have c14 := r4 h c40 c41 c01
    have c44 := r3 h c14 c11 c11
    exact k1 h c44 c14 c41 c40
  · have c20 := r4 h c04 c03 c40
    have c24 := r1 h c20 c02 c03
    exact kr h c20 c24
  · have c44 := r4 h c40 c41 c01
    have c12 := r3 h c41 c04 c44
    exact kr h c11 c12
  · exact k1 h c40 c54 c00 c40
  have c24 := r4 h c40 c41 c01
  rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
  · exact k1 h c41 c04 c12 c40
  · exact kr h c12 c15
  · have c42 := r1 h c41 c04 c12
    have c21 := r1 h c24 c12 c42
    exact k1 h c12 c21 c24 c11
  · exact kr h c12 c11
  · exact kr h c12 c10
  have c43 := r1 h c41 c04 c12
  have c21 := r1 h c24 c12 c43
  have c42 := r4 h c21 c24 c11
  exact kr h c42 c43

private theorem sym3 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 1) (c02 : op 0 2 = 3) : False := by
  rcases cv2 (op 0 3) with c03|c03|c03|c03|c03|c03
  · exact kr h c03 c00
  · exact kr h c03 c01
  · exact kr h c03 c02
  · exact sym2 h c00 c01 c02 c03
  · exact sym2 (h.cj (sw 4 5)) (cc c00) (cc c01) (cc c02) (cc c03)
  rcases cv4 (op 0 4) with c04|c04|c04|c04|c04|c04
  · exact kr h c04 c00
  · exact kr h c04 c01
  · exact kr h c04 c03
  · exact kr h c04 c02
  · exact n2 h c00 c01 c02 c03 c04
  have c05 := rc5 h 5 c00 c01 c03 c02 c04
  rcases cv5 (op 2 0) with c20|c20|c20|c20|c20|c20
  · have c22 := r1 h c20 c02 c03
    exact kr h c20 c22
  · have c31 := r3 h c03 c20 c02
    rcases cv5 (op 3 2) with c32|c32|c32|c32|c32|c32
    · have c22 := r3 h c32 c03 c31
      exact kr h c20 c22
    · have c13 := r4 h c32 c31 c20
      have c12 := r1 h c13 c01 c31
      have c22 := r1 h c20 c12 c03
      have c10 := r1 h c12 c31 c22
      exact k1 h c01 c10 c12 c03
    · exact kr h c32 c31
    · have c33 := r4 h c32 c31 c20
      exact k1 h c33 c03 c32 c33
    · have c43 := r4 h c32 c31 c20
      rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
      · exact k1 h c02 c30 c20 c01
      · have c21 := r3 h c02 c30 c03
        have c14 := r3 h c21 c32 c20
        have c23 := r4 h c31 c30 c14
        have c42 := r4 h c23 c21 c30
        exact kr h c42 c43
      · exact kr h c30 c31
      · have c23 := r3 h c02 c30 c03
        have c34 := r3 h c23 c32 c23
        exact k1 h c43 c04 c34 c43
      · exact kr h c30 c32
      have c25 := r3 h c02 c30 c03
      rcases cv5 (op 2 3) with c23|c23|c23|c23|c23|c23
      · have c33 := r3 h c23 c02 c25
        exact kr h c30 c33
      · exact kr h c23 c20
      · have c22 := r4 h c23 c25 c30
        exact k1 h c22 c02 c23 c22
      · exact kr h c23 c25
      · have c42 := r4 h c23 c25 c30
        exact kr h c42 c43
      have c52 := r4 h c23 c25 c30
      have c54 := r3 h c25 c32 c23
      have c53 := r1 h c52 c05 c25
      have c33 := r3 h c53 c25 c54
      exact kr h c32 c33
    have c53 := r4 h c32 c31 c20
    rcases cv4 (op 3 0) with c30|c30|c30|c30|c30|c30
    · exact k1 h c02 c30 c20 c01
    · have c21 := r3 h c02 c30 c03
      have c15 := r3 h c21 c32 c20
      have c23 := r4 h c31 c30 c15
      have c52 := r4 h c23 c21 c30
      exact kr h c52 c53
    · exact kr h c30 c31
    · have c23 := r3 h c02 c30 c03
      have c35 := r3 h c23 c32 c23
      exact k1 h c53 c05 c35 c53
    · exact kr h c30 c32
    have c24 := r3 h c02 c30 c03
    rcases cv4 (op 2 3) with c23|c23|c23|c23|c23|c23
    · have c33 := r3 h c23 c02 c24
      exact kr h c30 c33
    · exact kr h c23 c20
    · have c22 := r4 h c23 c24 c30
      exact k1 h c22 c02 c23 c22
    · exact kr h c23 c24
    · have c52 := r4 h c23 c24 c30
      exact kr h c52 c53
    have c42 := r4 h c23 c24 c30
    have c45 := r3 h c24 c32 c23
    have c43 := r1 h c42 c04 c24
    have c33 := r3 h c43 c24 c45
    exact kr h c32 c33
  · have c32 := r3 h c03 c20 c02
    have c23 := r4 h c32 c32 c20
    have c22 := r4 h c20 c23 c02
    exact kr h c20 c22
  · have c30 := r4 h c02 c03 c20
    have c33 := r3 h c03 c20 c02
    exact k1 h c30 c03 c02 c33
  · have c34 := r3 h c03 c20 c02
    rcases cv5 (op 3 2) with c32|c32|c32|c32|c32|c32
    · have c22 := r3 h c32 c03 c34
      exact kr h c20 c22
    · have c13 := r4 h c32 c34 c20
      rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
      · exact k1 h c02 c30 c20 c04
      · exact kr h c30 c32
      · exact kr h c30 c34
      · have c23 := r3 h c02 c30 c03
        have c31 := r3 h c23 c32 c23
        exact kr h c30 c31
      · have c24 := r3 h c02 c30 c03
        have c41 := r3 h c24 c32 c20
        have c23 := r4 h c34 c30 c41
        have c12 := r4 h c23 c24 c30
        exact kr h c12 c13
      have c25 := r3 h c02 c30 c03
      rcases cv5 (op 2 3) with c23|c23|c23|c23|c23|c23
      · have c33 := r3 h c23 c02 c25
        exact kr h c30 c33
      · have c12 := r4 h c23 c25 c30
        exact kr h c12 c13
      · have c22 := r4 h c23 c25 c30
        exact k1 h c22 c02 c23 c22
      · exact kr h c23 c25
      · exact kr h c23 c20
      have c52 := r4 h c23 c25 c30
      have c51 := r3 h c25 c32 c23
      have c53 := r1 h c52 c05 c25
      have c33 := r3 h c53 c25 c51
      exact kr h c32 c33
    · exact kr h c32 c34
    · have c33 := r4 h c32 c34 c20
      exact k1 h c33 c03 c32 c33
    · have c43 := r4 h c32 c34 c20
      have c42 := r1 h c43 c04 c34
      have c22 := r1 h c20 c42 c03
      have c40 := r1 h c42 c34 c22
      exact k1 h c04 c40 c42 c03
    have c53 := r4 h c32 c34 c20
    rcases cv1 (op 3 0) with c30|c30|c30|c30|c30|c30
    · exact k1 h c02 c30 c20 c04
    · exact kr h c30 c34
    · have c23 := r3 h c02 c30 c03
      have c35 := r3 h c23 c32 c23
      exact k1 h c53 c05 c35 c53
    · have c24 := r3 h c02 c30 c03
      have c45 := r3 h c24 c32 c20
      have c23 := r4 h c34 c30 c45
      have c52 := r4 h c23 c24 c30
      exact kr h c52 c53
    · exact kr h c30 c32
    have c21 := r3 h c02 c30 c03
    rcases cv1 (op 2 3) with c23|c23|c23|c23|c23|c23
    · have c33 := r3 h c23 c02 c21
      exact kr h c30 c33
    · have c22 := r4 h c23 c21 c30
      exact k1 h c22 c02 c23 c22
    · exact kr h c23 c21
    · exact kr h c23 c20
    · have c52 := r4 h c23 c21 c30
      exact kr h c52 c53
    have c15 := r3 h c21 c32 c23
    have c12 := r4 h c23 c21 c30
    have c13 := r1 h c12 c01 c21
    have c33 := r3 h c13 c21 c15
    exact kr h c32 c33
  have c35 := r3 h c03 c20 c02
  rcases cv4 (op 3 2) with c32|c32|c32|c32|c32|c32
  · have c22 := r3 h c32 c03 c35
    exact kr h c20 c22
  · have c13 := r4 h c32 c35 c20
    rcases cv4 (op 3 0) with c30|c30|c30|c30|c30|c30
    · exact k1 h c02 c30 c20 c05
    · exact kr h c30 c32
    · exact kr h c30 c35
    · have c23 := r3 h c02 c30 c03
      have c31 := r3 h c23 c32 c23
      exact kr h c30 c31
    · have c25 := r3 h c02 c30 c03
      have c51 := r3 h c25 c32 c20
      have c23 := r4 h c35 c30 c51
      have c12 := r4 h c23 c25 c30
      exact kr h c12 c13
    have c24 := r3 h c02 c30 c03
    rcases cv4 (op 2 3) with c23|c23|c23|c23|c23|c23
    · have c33 := r3 h c23 c02 c24
      exact kr h c30 c33
    · have c12 := r4 h c23 c24 c30
      exact kr h c12 c13
    · have c22 := r4 h c23 c24 c30
      exact k1 h c22 c02 c23 c22
    · exact kr h c23 c24
    · exact kr h c23 c20
    have c42 := r4 h c23 c24 c30
    have c41 := r3 h c24 c32 c23
    have c43 := r1 h c42 c04 c24
    have c33 := r3 h c43 c24 c41
    exact kr h c32 c33
  · exact kr h c32 c35
  · have c33 := r4 h c32 c35 c20
    exact k1 h c33 c03 c32 c33
  · have c53 := r4 h c32 c35 c20
    have c52 := r1 h c53 c05 c35
    have c22 := r1 h c20 c52 c03
    have c50 := r1 h c52 c35 c22
    exact k1 h c05 c50 c52 c03
  have c43 := r4 h c32 c35 c20
  rcases cv1 (op 3 0) with c30|c30|c30|c30|c30|c30
  · exact k1 h c02 c30 c20 c05
  · exact kr h c30 c35
  · have c23 := r3 h c02 c30 c03
    have c34 := r3 h c23 c32 c23
    exact k1 h c43 c04 c34 c43
  · exact kr h c30 c32
  · have c25 := r3 h c02 c30 c03
    have c54 := r3 h c25 c32 c20
    have c23 := r4 h c35 c30 c54
    have c42 := r4 h c23 c25 c30
    exact kr h c42 c43
  have c21 := r3 h c02 c30 c03
  rcases cv1 (op 2 3) with c23|c23|c23|c23|c23|c23
  · have c33 := r3 h c23 c02 c21
    exact kr h c30 c33
  · have c22 := r4 h c23 c21 c30
    exact k1 h c22 c02 c23 c22
  · exact kr h c23 c21
  · have c42 := r4 h c23 c21 c30
    exact kr h c42 c43
  · exact kr h c23 c20
  have c14 := r3 h c21 c32 c23
  have c12 := r4 h c23 c21 c30
  have c13 := r1 h c12 c01 c21
  have c33 := r3 h c13 c21 c14
  exact kr h c32 c33

private theorem n3 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 2) (c02 : op 0 2 = 1) (c03 : op 0 3 = 3) (c04 : op 0 4 = 5) : False := by
  have c05 := rc4 h 5 c00 c02 c01 c03 c04
  rcases cv4 (op 1 0) with c10|c10|c10|c10|c10|c10
  · have c11 := r1 h c10 c01 c02
    exact kr h c10 c11
  · have c21 := r3 h c02 c10 c01
    have c12 := r4 h c21 c21 c10
    have c11 := r4 h c10 c12 c01
    exact kr h c10 c11
  · have c20 := r4 h c01 c02 c10
    have c22 := r3 h c02 c10 c01
    exact k1 h c20 c02 c01 c22
  · have c23 := r3 h c02 c10 c01
    rcases cv5 (op 2 1) with c21|c21|c21|c21|c21|c21
    · have c11 := r3 h c21 c02 c23
      exact kr h c10 c11
    · exact kr h c21 c23
    · have c22 := r4 h c21 c23 c10
      exact k1 h c22 c02 c21 c22
    · have c32 := r4 h c21 c23 c10
      have c31 := r1 h c32 c03 c23
      have c11 := r1 h c10 c31 c02
      have c30 := r1 h c31 c23 c11
      exact k1 h c03 c30 c31 c02
    · have c42 := r4 h c21 c23 c10
      rcases cv5 (op 2 0) with c20|c20|c20|c20|c20|c20
      · exact k1 h c01 c20 c10 c03
      · exact kr h c20 c23
      · have c12 := r3 h c01 c20 c02
        have c24 := r3 h c12 c21 c12
        exact kr h c20 c24
      · have c13 := r3 h c01 c20 c02
        have c34 := r3 h c13 c21 c10
        have c12 := r4 h c23 c20 c34
        have c41 := r4 h c12 c13 c20
        exact kr h c41 c42
      · exact kr h c20 c21
      have c15 := r3 h c01 c20 c02
      rcases cv3 (op 3 1) with c31|c31|c31|c31|c31|c31
      · exact k1 h c10 c31 c00 c10
      · have c12 := r1 h c10 c31 c01
        have c22 := r3 h c12 c01 c15
        exact kr h c20 c22
      · have c11 := r1 h c10 c31 c02
        have c30 := r1 h c31 c23 c11
        exact k1 h c03 c30 c31 c02
      · exact k1 h c10 c31 c04 c15
      · have c14 := r1 h c10 c31 c05
        exact k1 h c14 c01 c42 c10
      have c13 := r1 h c10 c31 c03
      have c30 := r4 h c03 c03 c31
      exact k1 h c30 c13 c00 c30
    have c52 := r4 h c21 c23 c10
    rcases cv4 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c01 c20 c10 c03
    · exact kr h c20 c23
    · have c12 := r3 h c01 c20 c02
      have c25 := r3 h c12 c21 c12
      exact kr h c20 c25
    · have c13 := r3 h c01 c20 c02
      have c35 := r3 h c13 c21 c10
      have c12 := r4 h c23 c20 c35
      have c51 := r4 h c12 c13 c20
      exact kr h c51 c52
    · exact kr h c20 c21
    have c14 := r3 h c01 c20 c02
    rcases cv3 (op 3 1) with c31|c31|c31|c31|c31|c31
    · exact k1 h c10 c31 c00 c10
    · have c12 := r1 h c10 c31 c01
      have c22 := r3 h c12 c01 c14
      exact kr h c20 c22
    · have c11 := r1 h c10 c31 c02
      have c30 := r1 h c31 c23 c11
      exact k1 h c03 c30 c31 c02
    · have c15 := r1 h c10 c31 c04
      exact k1 h c15 c01 c52 c10
    · exact k1 h c10 c31 c05 c14
    have c13 := r1 h c10 c31 c03
    have c30 := r4 h c03 c03 c31
    exact k1 h c30 c13 c00 c30
  · have c25 := r3 h c02 c10 c01
    rcases cv4 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c01 c20 c10 c05
    · exact kr h c20 c25
    · have c12 := r3 h c01 c20 c02
      have c21 := r4 h c12 c12 c20
      have c11 := r3 h c21 c02 c25
      exact kr h c10 c11
    · have c13 := r3 h c01 c20 c02
      rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c22 := r3 h c12 c01 c13
        exact kr h c20 c22
      · have c11 := r4 h c12 c13 c20
        exact k1 h c11 c01 c12 c11
      · exact kr h c12 c13
      · have c31 := r4 h c12 c13 c20
        have c32 := r1 h c31 c03 c13
        have c22 := r1 h c20 c32 c01
        have c30 := r1 h c32 c13 c22
        exact k1 h c03 c30 c32 c01
      · exact kr h c12 c10
      have c41 := r4 h c12 c13 c20
      rcases cv3 (op 3 2) with c32|c32|c32|c32|c32|c32
      · exact k1 h c20 c32 c00 c20
      · have c22 := r1 h c20 c32 c01
        have c30 := r1 h c32 c13 c22
        exact k1 h c03 c30 c32 c01
      · have c21 := r1 h c20 c32 c02
        have c11 := r3 h c21 c02 c25
        exact kr h c10 c11
      · exact k1 h c20 c32 c04 c25
      · have c24 := r1 h c20 c32 c05
        exact k1 h c24 c02 c41 c20
      have c23 := r1 h c20 c32 c03
      have c30 := r4 h c03 c03 c32
      exact k1 h c30 c23 c00 c30
    · have c15 := r3 h c01 c20 c02
      rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c51 := r4 h c10 c12 c01
        have c50 := r1 h c51 c15 c12
        have c21 := r1 h c25 c12 c50
        exact kr h c20 c21
      · have c51 := r3 h c25 c12 c20
        exact k1 h c10 c51 c00 c10
      · exact kr h c12 c15
      · have c31 := r4 h c12 c15 c20
        have c53 := r3 h c25 c12 c20
        have c21 := r4 h c15 c10 c53
        have c32 := r4 h c21 c25 c10
        exact kr h c31 c32
      · exact kr h c12 c10
      have c41 := r4 h c12 c15 c20
      have c54 := r3 h c25 c12 c20
      have c42 := r1 h c41 c04 c15
      have c21 := r4 h c15 c10 c54
      have c11 := r3 h c21 c42 c25
      exact kr h c10 c11
    have c14 := r3 h c01 c20 c02
    rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c22 := r3 h c12 c01 c14
      exact kr h c20 c22
    · have c11 := r4 h c12 c14 c20
      exact k1 h c11 c01 c12 c11
    · exact kr h c12 c14
    · have c31 := r4 h c12 c14 c20
      rcases cv4 (op 1 3) with c13|c13|c13|c13|c13|c13
      · have c30 := r1 h c31 c03 c13
        exact k1 h c03 c30 c31 c00
      · exact k1 h c31 c03 c13 c31
      · exact kr h c13 c14
      · exact kr h c13 c12
      · exact kr h c13 c10
      have c34 := r1 h c31 c03 c13
      rcases cv1 (op 1 1) with c11|c11|c11|c11|c11|c11
      · exact k1 h c11 c01 c12 c13
      · exact kr h c11 c14
      · exact kr h c11 c12
      · exact kr h c11 c13
      · exact kr h c11 c10
      have c15 := rc0 h 5 c11 c14 c12 c13 c10
      have c51 := r4 h c10 c15 c04
      have c40 := r4 h c05 c04 c51
      have c41 := r1 h c40 c14 c02
      have c30 := r3 h c13 c41 c12
      have c32 := r3 h c03 c30 c03
      rcases cv4 (op 3 3) with c33|c33|c33|c33|c33|c33
      · exact kr h c33 c31
      · exact kr h c33 c34
      · exact kr h c33 c30
      · exact kr h c33 c32
      · exact k1 h c32 c33 c25 c31
      have c44 := r3 h c34 c13 c33
      exact k1 h c44 c34 c41 c40
    · exact kr h c12 c10
    have c41 := r4 h c12 c14 c20
    rcases cv1 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c12 c14
    · exact kr h c11 c14
    · rcases cv1 (op 1 3) with c13|c13|c13|c13|c13|c13
      · have c15 := rc1 h 5 c13 c14 c11 c12 c10
        exact k1 h c41 c04 c15 c41
      · exact kr h c13 c14
      · exact kr h c13 c11
      · exact kr h c13 c12
      · exact kr h c13 c10
      have c31 := r4 h c11 c13 c11
      have c33 := r1 h c31 c13 c11
      exact k1 h c33 c13 c31 c31
    · exact kr h c11 c12
    · exact kr h c11 c10
    rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
    · exact kr h c13 c11
    · exact kr h c13 c14
    · rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
      · exact k1 h c03 c30 c30 c00
      · have c33 := r1 h c30 c13 c03
        have c31 := r3 h c03 c30 c03
        exact k1 h c13 c31 c33 c10
      · have c32 := r3 h c03 c30 c03
        have c31 := r4 h c13 c13 c32
        exact kr h c30 c31
      · have c33 := r3 h c03 c30 c03
        exact kr h c30 c33
      · have c34 := r3 h c03 c30 c03
        have c31 := r4 h c13 c13 c34
        exact kr h c30 c31
      have c35 := r3 h c03 c30 c03
      have c31 := r4 h c13 c13 c35
      exact kr h c30 c31
    · exact kr h c13 c12
    · exact kr h c13 c10
    have c15 := rc3 h 5 c13 c11 c14 c12 c10
    have c43 := r1 h c41 c04 c15
    have c32 := r3 h c13 c01 c15
    have c45 := r1 h c43 c14 c32
    rcases cv4 (op 4 0) with c40|c40|c40|c40|c40|c40
    · exact kr h c40 c41
    · exact kr h c40 c43
    · have c24 := r4 h c40 c41 c02
      have c22 := r4 h c24 c20 c41
      exact kr h c22 c25
    · exact kr h c40 c45
    · have c54 := r4 h c40 c41 c02
      have c50 := r4 h c04 c05 c40
      exact k1 h c54 c25 c41 c50
    have c44 := r4 h c40 c41 c02
    have c24 := r4 h c44 c40 c41
    have c54 := r3 h c05 c40 c04
    exact k1 h c25 c12 c54 c24
  have c24 := r3 h c02 c10 c01
  rcases cv5 (op 2 0) with c20|c20|c20|c20|c20|c20
  · exact k1 h c01 c20 c10 c04
  · exact kr h c20 c24
  · have c12 := r3 h c01 c20 c02
    have c21 := r4 h c12 c12 c20
    have c11 := r3 h c21 c02 c24
    exact kr h c10 c11
  · have c13 := r3 h c01 c20 c02
    rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c22 := r3 h c12 c01 c13
      exact kr h c20 c22
    · have c11 := r4 h c12 c13 c20
      exact k1 h c11 c01 c12 c11
    · exact kr h c12 c13
    · have c31 := r4 h c12 c13 c20
      have c32 := r1 h c31 c03 c13
      have c22 := r1 h c20 c32 c01
      have c30 := r1 h c32 c13 c22
      exact k1 h c03 c30 c32 c01
    · exact kr h c12 c10
    have c51 := r4 h c12 c13 c20
    rcases cv3 (op 3 2) with c32|c32|c32|c32|c32|c32
    · exact k1 h c20 c32 c00 c20
    · have c22 := r1 h c20 c32 c01
      have c30 := r1 h c32 c13 c22
      exact k1 h c03 c30 c32 c01
    · have c21 := r1 h c20 c32 c02
      have c11 := r3 h c21 c02 c24
      exact kr h c10 c11
    · have c25 := r1 h c20 c32 c04
      exact k1 h c25 c02 c51 c20
    · exact k1 h c20 c32 c05 c24
    have c23 := r1 h c20 c32 c03
    have c30 := r4 h c03 c03 c32
    exact k1 h c30 c23 c00 c30
  · have c14 := r3 h c01 c20 c02
    rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c41 := r4 h c10 c12 c01
      have c40 := r1 h c41 c14 c12
      have c21 := r1 h c24 c12 c40
      exact kr h c20 c21
    · have c41 := r3 h c24 c12 c20
      exact k1 h c10 c41 c00 c10
    · exact kr h c12 c14
    · have c31 := r4 h c12 c14 c20
      have c43 := r3 h c24 c12 c20
      have c21 := r4 h c14 c10 c43
      have c32 := r4 h c21 c24 c10
      exact kr h c31 c32
    · exact kr h c12 c10
    have c51 := r4 h c12 c14 c20
    have c45 := r3 h c24 c12 c20
    have c52 := r1 h c51 c05 c14
    have c21 := r4 h c14 c10 c45
    have c11 := r3 h c21 c52 c24
    exact kr h c10 c11
  have c15 := r3 h c01 c20 c02
  rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
  · have c22 := r3 h c12 c01 c15
    exact kr h c20 c22
  · have c11 := r4 h c12 c15 c20
    exact k1 h c11 c01 c12 c11
  · exact kr h c12 c15
  · have c31 := r4 h c12 c15 c20
    rcases cv5 (op 1 3) with c13|c13|c13|c13|c13|c13
    · have c30 := r1 h c31 c03 c13
      exact k1 h c03 c30 c31 c00
    · exact k1 h c31 c03 c13 c31
    · exact kr h c13 c15
    · exact kr h c13 c12
    · exact kr h c13 c10
    have c35 := r1 h c31 c03 c13
    rcases cv1 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c12 c13
    · exact kr h c11 c15
    · exact kr h c11 c12
    · exact kr h c11 c10
    · exact kr h c11 c13
    have c14 := rc0 h 4 c11 c15 c12 c10 c13
    have c41 := r4 h c10 c14 c05
    have c50 := r4 h c04 c05 c41
    have c51 := r1 h c50 c15 c02
    have c30 := r3 h c13 c51 c12
    have c32 := r3 h c03 c30 c03
    rcases cv5 (op 3 3) with c33|c33|c33|c33|c33|c33
    · exact kr h c33 c31
    · exact kr h c33 c35
    · exact kr h c33 c30
    · exact kr h c33 c32
    · exact k1 h c32 c33 c24 c31
    have c34 := rc4 h 4 c31 c35 c30 c32 c33
    have c53 := r4 h c33 c32 c30
    have c54 := r1 h c53 c05 c34
    have c55 := r1 h c54 c35 c41
    exact k1 h c35 c13 c55 c34
  · exact kr h c12 c10
  have c51 := r4 h c12 c15 c20
  rcases cv1 (op 1 1) with c11|c11|c11|c11|c11|c11
  · exact k1 h c11 c01 c12 c15
  · exact kr h c11 c15
  · rcases cv1 (op 1 3) with c13|c13|c13|c13|c13|c13
    · have c14 := rc1 h 4 c13 c15 c11 c10 c12
      exact k1 h c51 c05 c14 c51
    · exact kr h c13 c15
    · exact kr h c13 c11
    · exact kr h c13 c10
    · exact kr h c13 c12
    have c31 := r4 h c11 c13 c11
    have c33 := r1 h c31 c13 c11
    exact k1 h c33 c13 c31 c31
  · exact kr h c11 c10
  · exact kr h c11 c12
  rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
  · exact kr h c13 c11
  · exact kr h c13 c15
  · rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
    · exact k1 h c03 c30 c30 c00
    · have c33 := r1 h c30 c13 c03
      have c31 := r3 h c03 c30 c03
      exact k1 h c13 c31 c33 c10
    · have c32 := r3 h c03 c30 c03
      have c31 := r4 h c13 c13 c32
      exact kr h c30 c31
    · have c33 := r3 h c03 c30 c03
      exact kr h c30 c33
    · have c34 := r3 h c03 c30 c03
      have c31 := r4 h c13 c13 c34
      exact kr h c30 c31
    have c35 := r3 h c03 c30 c03
    have c31 := r4 h c13 c13 c35
    exact kr h c30 c31
  · exact kr h c13 c10
  · exact kr h c13 c12
  have c14 := rc3 h 4 c13 c11 c15 c10 c12
  have c41 := r4 h c10 c13 c03
  have c53 := r1 h c51 c05 c14
  have c32 := r3 h c13 c01 c14
  have c54 := r1 h c53 c15 c32
  rcases cv4 (op 5 0) with c50|c50|c50|c50|c50|c50
  · exact kr h c50 c51
  · exact kr h c50 c53
  · have c25 := r4 h c50 c51 c02
    have c22 := r4 h c25 c20 c51
    exact kr h c22 c24
  · exact kr h c50 c54
  · have c45 := r3 h c04 c50 c05
    exact k1 h c45 c54 c53 c41
  have c45 := r4 h c50 c51 c02
  have c40 := r4 h c05 c04 c50
  exact k1 h c45 c24 c51 c40

private theorem n4 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 2) (c02 : op 0 2 = 1) (c03 : op 0 3 = 4) (c04 : op 0 4 = 3) : False := by
  have c05 := rc5 h 5 c00 c02 c01 c04 c03
  rcases cv4 (op 1 0) with c10|c10|c10|c10|c10|c10
  · have c11 := r1 h c10 c01 c02
    exact kr h c10 c11
  · have c21 := r3 h c02 c10 c01
    have c12 := r4 h c21 c21 c10
    have c11 := r4 h c10 c12 c01
    exact kr h c10 c11
  · have c20 := r4 h c01 c02 c10
    have c22 := r3 h c02 c10 c01
    exact k1 h c20 c02 c01 c22
  · have c23 := r3 h c02 c10 c01
    rcases cv4 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c01 c20 c10 c03
    · exact kr h c20 c23
    · have c12 := r3 h c01 c20 c02
      have c21 := r4 h c12 c12 c20
      have c11 := r3 h c21 c02 c23
      exact kr h c10 c11
    · have c13 := r3 h c01 c20 c02
      rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c31 := r4 h c10 c12 c01
        have c30 := r1 h c31 c13 c12
        have c21 := r1 h c23 c12 c30
        exact kr h c20 c21
      · have c31 := r3 h c23 c12 c20
        exact k1 h c10 c31 c00 c10
      · exact kr h c12 c13
      · exact kr h c12 c10
      · have c51 := r4 h c12 c13 c20
        have c35 := r3 h c23 c12 c20
        have c21 := r4 h c13 c10 c35
        have c52 := r4 h c21 c23 c10
        exact kr h c51 c52
      have c41 := r4 h c12 c13 c20
      have c34 := r3 h c23 c12 c20
      have c42 := r1 h c41 c04 c13
      have c21 := r4 h c13 c10 c34
      have c11 := r3 h c21 c42 c23
      exact kr h c10 c11
    · have c15 := r3 h c01 c20 c02
      rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c22 := r3 h c12 c01 c15
        exact kr h c20 c22
      · have c11 := r4 h c12 c15 c20
        exact k1 h c11 c01 c12 c11
      · exact kr h c12 c15
      · exact kr h c12 c10
      · have c51 := r4 h c12 c15 c20
        have c52 := r1 h c51 c05 c15
        have c22 := r1 h c20 c52 c01
        have c50 := r1 h c52 c15 c22
        exact k1 h c05 c50 c52 c01
      have c41 := r4 h c12 c15 c20
      rcases cv5 (op 5 2) with c52|c52|c52|c52|c52|c52
      · exact k1 h c20 c52 c00 c20
      · have c22 := r1 h c20 c52 c01
        have c50 := r1 h c52 c15 c22
        exact k1 h c05 c50 c52 c01
      · have c21 := r1 h c20 c52 c02
        have c11 := r3 h c21 c02 c23
        exact kr h c10 c11
      · have c24 := r1 h c20 c52 c03
        exact k1 h c24 c02 c41 c20
      · exact k1 h c20 c52 c04 c23
      have c25 := r1 h c20 c52 c05
      have c50 := r4 h c05 c05 c52
      exact k1 h c50 c25 c00 c50
    have c14 := r3 h c01 c20 c02
    rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c22 := r3 h c12 c01 c14
      exact kr h c20 c22
    · have c11 := r4 h c12 c14 c20
      exact k1 h c11 c01 c12 c11
    · exact kr h c12 c14
    · exact kr h c12 c10
    · have c51 := r4 h c12 c14 c20
      rcases cv4 (op 1 5) with c15|c15|c15|c15|c15|c15
      · have c50 := r1 h c51 c05 c15
        exact k1 h c05 c50 c51 c00
      · exact k1 h c51 c05 c15 c51
      · exact kr h c15 c14
      · exact kr h c15 c10
      · exact kr h c15 c12
      have c54 := r1 h c51 c05 c15
      rcases cv1 (op 1 1) with c11|c11|c11|c11|c11|c11
      · exact k1 h c11 c01 c12 c15
      · exact kr h c11 c14
      · exact kr h c11 c10
      · exact kr h c11 c15
      · exact kr h c11 c12
      have c13 := rc0 h 3 c11 c14 c10 c15 c12
      have c31 := r4 h c10 c13 c04
      have c40 := r4 h c03 c04 c31
      have c41 := r1 h c40 c14 c02
      have c50 := r3 h c15 c41 c12
      have c52 := r3 h c05 c50 c05
      rcases cv3 (op 5 3) with c53|c53|c53|c53|c53|c53
      · exact kr h c53 c51
      · exact kr h c53 c54
      · exact kr h c53 c50
      · have c55 := rc3 h 5 c51 c54 c50 c53 c52
        exact k1 h c52 c55 c23 c51
      · exact kr h c53 c52
      have c55 := rc4 h 5 c51 c54 c50 c53 c52
      have c45 := r4 h c55 c52 c50
      exact kr h c41 c45
    have c41 := r4 h c12 c14 c20
    rcases cv1 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c12 c14
    · exact kr h c11 c14
    · exact kr h c11 c10
    · exact kr h c11 c12
    · rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact k1 h c41 c04 c13 c41
      · exact kr h c13 c14
      · exact kr h c13 c10
      · exact kr h c13 c12
      · exact kr h c13 c11
      have c15 := rc1 h 5 c13 c14 c10 c12 c11
      have c51 := r4 h c11 c15 c11
      have c55 := r1 h c51 c15 c11
      exact k1 h c55 c15 c51 c51
    rcases cv5 (op 1 3) with c13|c13|c13|c13|c13|c13
    · have c15 := rc5 h 5 c13 c11 c14 c10 c12
      rcases cv4 (op 5 0) with c50|c50|c50|c50|c50|c50
      · exact k1 h c05 c50 c50 c00
      · have c55 := r1 h c50 c15 c05
        have c51 := r3 h c05 c50 c05
        exact k1 h c15 c51 c55 c10
      · have c52 := r3 h c05 c50 c05
        have c51 := r4 h c15 c15 c52
        exact kr h c50 c51
      · have c53 := r3 h c05 c50 c05
        have c51 := r4 h c15 c15 c53
        exact kr h c50 c51
      · have c55 := r3 h c05 c50 c05
        exact kr h c50 c55
      have c54 := r3 h c05 c50 c05
      have c51 := r4 h c15 c15 c54
      exact kr h c50 c51
    · exact kr h c13 c11
    · exact kr h c13 c14
    · exact kr h c13 c10
    · exact kr h c13 c12
    have c15 := rc0 h 5 c11 c14 c10 c12 c13
    have c31 := r4 h c10 c15 c05
    have c45 := r1 h c41 c04 c13
    have c52 := r3 h c15 c01 c13
    have c43 := r1 h c45 c14 c52
    rcases cv3 (op 4 0) with c40|c40|c40|c40|c40|c40
    · exact kr h c40 c41
    · exact kr h c40 c45
    · have c24 := r4 h c40 c41 c02
      have c22 := r4 h c24 c20 c41
      exact kr h c22 c23
    · have c34 := r3 h c03 c40 c04
      exact k1 h c34 c43 c45 c31
    · exact kr h c40 c43
    have c34 := r4 h c40 c41 c02
    have c30 := r4 h c04 c03 c40
    exact k1 h c34 c23 c41 c30
  · have c25 := r3 h c02 c10 c01
    rcases cv4 (op 2 1) with c21|c21|c21|c21|c21|c21
    · have c11 := r3 h c21 c02 c25
      exact kr h c10 c11
    · exact kr h c21 c25
    · have c22 := r4 h c21 c25 c10
      exact k1 h c22 c02 c21 c22
    · have c32 := r4 h c21 c25 c10
      rcases cv4 (op 2 0) with c20|c20|c20|c20|c20|c20
      · exact k1 h c01 c20 c10 c05
      · exact kr h c20 c25
      · have c12 := r3 h c01 c20 c02
        have c23 := r3 h c12 c21 c12
        exact kr h c20 c23
      · exact kr h c20 c21
      · have c15 := r3 h c01 c20 c02
        have c53 := r3 h c15 c21 c10
        have c12 := r4 h c25 c20 c53
        have c31 := r4 h c12 c15 c20
        exact kr h c31 c32
      have c14 := r3 h c01 c20 c02
      rcases cv5 (op 5 1) with c51|c51|c51|c51|c51|c51
      · exact k1 h c10 c51 c00 c10
      · have c12 := r1 h c10 c51 c01
        have c22 := r3 h c12 c01 c14
        exact kr h c20 c22
      · have c11 := r1 h c10 c51 c02
        have c50 := r1 h c51 c25 c11
        exact k1 h c05 c50 c51 c02
      · exact k1 h c10 c51 c03 c14
      · have c13 := r1 h c10 c51 c04
        exact k1 h c13 c01 c32 c10
      have c15 := r1 h c10 c51 c05
      have c50 := r4 h c05 c05 c51
      exact k1 h c50 c15 c00 c50
    · have c52 := r4 h c21 c25 c10
      have c51 := r1 h c52 c05 c25
      have c11 := r1 h c10 c51 c02
      have c50 := r1 h c51 c25 c11
      exact k1 h c05 c50 c51 c02
    have c42 := r4 h c21 c25 c10
    rcases cv3 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c01 c20 c10 c05
    · exact kr h c20 c25
    · have c12 := r3 h c01 c20 c02
      have c24 := r3 h c12 c21 c12
      exact kr h c20 c24
    · exact kr h c20 c21
    · have c15 := r3 h c01 c20 c02
      have c54 := r3 h c15 c21 c10
      have c12 := r4 h c25 c20 c54
      have c41 := r4 h c12 c15 c20
      exact kr h c41 c42
    have c13 := r3 h c01 c20 c02
    rcases cv5 (op 5 1) with c51|c51|c51|c51|c51|c51
    · exact k1 h c10 c51 c00 c10
    · have c12 := r1 h c10 c51 c01
      have c22 := r3 h c12 c01 c13
      exact kr h c20 c22
    · have c11 := r1 h c10 c51 c02
      have c50 := r1 h c51 c25 c11
      exact k1 h c05 c50 c51 c02
    · have c14 := r1 h c10 c51 c03
      exact k1 h c14 c01 c42 c10
    · exact k1 h c10 c51 c04 c13
    have c15 := r1 h c10 c51 c05
    have c50 := r4 h c05 c05 c51
    exact k1 h c50 c15 c00 c50
  have c24 := r3 h c02 c10 c01
  rcases cv3 (op 2 0) with c20|c20|c20|c20|c20|c20
  · exact k1 h c01 c20 c10 c04
  · exact kr h c20 c24
  · have c12 := r3 h c01 c20 c02
    have c21 := r4 h c12 c12 c20
    have c11 := r3 h c21 c02 c24
    exact kr h c10 c11
  · have c14 := r3 h c01 c20 c02
    rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c41 := r4 h c10 c12 c01
      have c40 := r1 h c41 c14 c12
      have c21 := r1 h c24 c12 c40
      exact kr h c20 c21
    · have c41 := r3 h c24 c12 c20
      exact k1 h c10 c41 c00 c10
    · exact kr h c12 c14
    · exact kr h c12 c10
    · have c51 := r4 h c12 c14 c20
      have c45 := r3 h c24 c12 c20
      have c21 := r4 h c14 c10 c45
      have c52 := r4 h c21 c24 c10
      exact kr h c51 c52
    have c31 := r4 h c12 c14 c20
    have c43 := r3 h c24 c12 c20
    have c32 := r1 h c31 c03 c14
    have c21 := r4 h c14 c10 c43
    have c11 := r3 h c21 c32 c24
    exact kr h c10 c11
  · have c15 := r3 h c01 c20 c02
    rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c22 := r3 h c12 c01 c15
      exact kr h c20 c22
    · have c11 := r4 h c12 c15 c20
      exact k1 h c11 c01 c12 c11
    · exact kr h c12 c15
    · exact kr h c12 c10
    · have c51 := r4 h c12 c15 c20
      have c52 := r1 h c51 c05 c15
      have c22 := r1 h c20 c52 c01
      have c50 := r1 h c52 c15 c22
      exact k1 h c05 c50 c52 c01
    have c31 := r4 h c12 c15 c20
    rcases cv5 (op 5 2) with c52|c52|c52|c52|c52|c52
    · exact k1 h c20 c52 c00 c20
    · have c22 := r1 h c20 c52 c01
      have c50 := r1 h c52 c15 c22
      exact k1 h c05 c50 c52 c01
    · have c21 := r1 h c20 c52 c02
      have c11 := r3 h c21 c02 c24
      exact kr h c10 c11
    · exact k1 h c20 c52 c03 c24
    · have c23 := r1 h c20 c52 c04
      exact k1 h c23 c02 c31 c20
    have c25 := r1 h c20 c52 c05
    have c50 := r4 h c05 c05 c52
    exact k1 h c50 c25 c00 c50
  have c13 := r3 h c01 c20 c02
  rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
  · have c22 := r3 h c12 c01 c13
    exact kr h c20 c22
  · have c11 := r4 h c12 c13 c20
    exact k1 h c11 c01 c12 c11
  · exact kr h c12 c13
  · exact kr h c12 c10
  · have c51 := r4 h c12 c13 c20
    rcases cv3 (op 1 5) with c15|c15|c15|c15|c15|c15
    · have c50 := r1 h c51 c05 c15
      exact k1 h c05 c50 c51 c00
    · exact k1 h c51 c05 c15 c51
    · exact kr h c15 c13
    · exact kr h c15 c10
    · exact kr h c15 c12
    have c53 := r1 h c51 c05 c15
    rcases cv1 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c11 c01 c12 c15
    · exact kr h c11 c13
    · exact kr h c11 c15
    · exact kr h c11 c10
    · exact kr h c11 c12
    have c14 := rc0 h 4 c11 c13 c15 c10 c12
    have c41 := r4 h c10 c14 c03
    have c30 := r4 h c04 c03 c41
    have c31 := r1 h c30 c13 c02
    have c50 := r3 h c15 c31 c12
    have c52 := r3 h c05 c50 c05
    rcases cv4 (op 5 4) with c54|c54|c54|c54|c54|c54
    · exact kr h c54 c51
    · exact kr h c54 c53
    · exact kr h c54 c50
    · have c55 := rc4 h 5 c51 c53 c50 c54 c52
      exact k1 h c52 c55 c24 c51
    · exact kr h c54 c52
    have c55 := rc3 h 5 c51 c53 c50 c54 c52
    have c35 := r4 h c55 c52 c50
    exact kr h c31 c35
  have c31 := r4 h c12 c13 c20
  rcases cv1 (op 1 1) with c11|c11|c11|c11|c11|c11
  · exact k1 h c11 c01 c12 c13
  · exact kr h c11 c13
  · exact kr h c11 c12
  · exact kr h c11 c10
  · rcases cv0 (op 1 4) with c14|c14|c14|c14|c14|c14
    · exact k1 h c31 c03 c14 c31
    · exact kr h c14 c13
    · exact kr h c14 c12
    · exact kr h c14 c10
    · exact kr h c14 c11
    have c15 := rc1 h 5 c14 c13 c12 c10 c11
    have c51 := r4 h c11 c15 c11
    have c55 := r1 h c51 c15 c11
    exact k1 h c55 c15 c51 c51
  rcases cv5 (op 1 4) with c14|c14|c14|c14|c14|c14
  · have c15 := rc5 h 5 c14 c11 c13 c12 c10
    rcases cv4 (op 5 0) with c50|c50|c50|c50|c50|c50
    · exact k1 h c05 c50 c50 c00
    · have c55 := r1 h c50 c15 c05
      have c51 := r3 h c05 c50 c05
      exact k1 h c15 c51 c55 c10
    · have c52 := r3 h c05 c50 c05
      have c51 := r4 h c15 c15 c52
      exact kr h c50 c51
    · have c53 := r3 h c05 c50 c05
      have c51 := r4 h c15 c15 c53
      exact kr h c50 c51
    · have c55 := r3 h c05 c50 c05
      exact kr h c50 c55
    have c54 := r3 h c05 c50 c05
    have c51 := r4 h c15 c15 c54
    exact kr h c50 c51
  · exact kr h c14 c11
  · exact kr h c14 c13
  · exact kr h c14 c12
  · exact kr h c14 c10
  have c15 := rc0 h 5 c11 c13 c12 c10 c14
  have c35 := r1 h c31 c03 c14
  have c52 := r3 h c15 c01 c14
  have c34 := r1 h c35 c13 c52
  rcases cv3 (op 3 0) with c30|c30|c30|c30|c30|c30
  · exact kr h c30 c31
  · exact kr h c30 c35
  · have c23 := r4 h c30 c31 c02
    have c22 := r4 h c23 c20 c31
    exact kr h c22 c24
  · have c43 := r4 h c30 c31 c02
    have c40 := r4 h c03 c04 c30
    exact k1 h c43 c24 c31 c40
  · exact kr h c30 c34
  have c33 := r4 h c30 c31 c02
  have c23 := r4 h c33 c30 c31
  have c43 := r3 h c04 c30 c03
  exact k1 h c24 c12 c43 c23

private theorem n5 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 2) (c02 : op 0 2 = 1) (c03 : op 0 3 = 4) (c04 : op 0 4 = 5) : False := by
  have c05 := rc3 h 5 c00 c02 c01 c03 c04
  rcases cv3 (op 1 0) with c10|c10|c10|c10|c10|c10
  · have c11 := r1 h c10 c01 c02
    exact kr h c10 c11
  · have c21 := r3 h c02 c10 c01
    have c12 := r4 h c21 c21 c10
    have c11 := r4 h c10 c12 c01
    exact kr h c10 c11
  · have c20 := r4 h c01 c02 c10
    have c22 := r3 h c02 c10 c01
    exact k1 h c20 c02 c01 c22
  · have c24 := r3 h c02 c10 c01
    rcases cv3 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c01 c20 c10 c04
    · exact kr h c20 c24
    · have c12 := r3 h c01 c20 c02
      have c21 := r4 h c12 c12 c20
      have c11 := r3 h c21 c02 c24
      exact kr h c10 c11
    · have c14 := r3 h c01 c20 c02
      rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c41 := r4 h c10 c12 c01
        have c40 := r1 h c41 c14 c12
        have c21 := r1 h c24 c12 c40
        exact kr h c20 c21
      · have c41 := r3 h c24 c12 c20
        exact k1 h c10 c41 c00 c10
      · exact kr h c12 c14
      · exact kr h c12 c10
      · have c51 := r4 h c12 c14 c20
        have c45 := r3 h c24 c12 c20
        have c21 := r4 h c14 c10 c45
        have c52 := r4 h c21 c24 c10
        exact kr h c51 c52
      have c31 := r4 h c12 c14 c20
      have c43 := r3 h c24 c12 c20
      have c32 := r1 h c31 c03 c14
      have c21 := r4 h c14 c10 c43
      have c11 := r3 h c21 c32 c24
      exact kr h c10 c11
    · have c15 := r3 h c01 c20 c02
      rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c22 := r3 h c12 c01 c15
        exact kr h c20 c22
      · have c11 := r4 h c12 c15 c20
        exact k1 h c11 c01 c12 c11
      · exact kr h c12 c15
      · exact kr h c12 c10
      · have c51 := r4 h c12 c15 c20
        rcases cv3 (op 4 1) with c41|c41|c41|c41|c41|c41
        · exact k1 h c10 c41 c00 c10
        · exact k1 h c10 c41 c01 c12
        · have c11 := r1 h c10 c41 c02
          exact k1 h c11 c01 c12 c15
        · exact k1 h c10 c41 c04 c15
        · have c13 := r1 h c10 c41 c05
          have c50 := r1 h c51 c05 c13
          exact k1 h c04 c50 c41 c05
        have c14 := r1 h c10 c41 c03
        have c50 := r4 h c04 c03 c41
        have c13 := r3 h c51 c05 c50
        exact kr h c13 c14
      have c31 := r4 h c12 c15 c20
      rcases cv5 (op 1 4) with c14|c14|c14|c14|c14|c14
      · have c41 := r4 h c10 c14 c03
        have c30 := r1 h c31 c03 c14
        have c50 := r4 h c04 c03 c41
        have c51 := r3 h c05 c30 c04
        exact k1 h c50 c15 c02 c51
      · exact k1 h c31 c03 c14 c31
      · exact kr h c14 c15
      · exact kr h c14 c12
      · exact kr h c14 c10
      have c35 := r1 h c31 c03 c14
      rcases cv4 (op 2 1) with c21|c21|c21|c21|c21|c21
      · have c11 := r3 h c21 c02 c24
        exact kr h c10 c11
      · exact kr h c21 c24
      · have c22 := r4 h c21 c24 c10
        exact k1 h c22 c02 c21 c22
      · have c32 := r4 h c21 c24 c10
        exact k1 h c32 c03 c24 c31
      · exact kr h c21 c20
      have c43 := r3 h c24 c12 c21
      have c41 := r1 h c43 c14 c35
      exact k1 h c10 c41 c03 c14
    have c13 := r3 h c01 c20 c02
    rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c22 := r3 h c12 c01 c13
      exact kr h c20 c22
    · have c11 := r4 h c12 c13 c20
      exact k1 h c11 c01 c12 c11
    · exact kr h c12 c13
    · exact kr h c12 c10
    · have c51 := r4 h c12 c13 c20
      have c52 := r1 h c51 c05 c13
      rcases cv5 (op 3 2) with c32|c32|c32|c32|c32|c32
      · exact k1 h c20 c32 c00 c20
      · have c22 := r1 h c20 c32 c01
        have c30 := r1 h c32 c13 c22
        exact k1 h c05 c30 c52 c01
      · have c21 := r1 h c20 c32 c02
        have c11 := r3 h c21 c02 c24
        exact kr h c10 c11
      · exact k1 h c20 c32 c03 c24
      · have c25 := r1 h c20 c32 c04
        exact k1 h c25 c02 c51 c20
      have c40 := r4 h c03 c05 c32
      have c42 := r1 h c40 c24 c01
      have c25 := r3 h c42 c04 c40
      exact k1 h c25 c02 c51 c20
    have c31 := r4 h c12 c13 c20
    rcases cv1 (op 3 0) with c30|c30|c30|c30|c30|c30
    · exact kr h c30 c31
    · have c23 := r4 h c30 c31 c02
      have c22 := r4 h c23 c20 c31
      exact kr h c22 c24
    · have c33 := r4 h c30 c31 c02
      have c21 := r4 h c13 c12 c33
      exact kr h c20 c21
    · have c43 := r4 h c30 c31 c02
      have c40 := r1 h c43 c24 c31
      have c50 := r4 h c04 c03 c40
      have c54 := r3 h c05 c30 c04
      exact k1 h c50 c05 c03 c54
    · have c40 := r4 h c03 c05 c30
      have c43 := r1 h c40 c04 c05
      exact k1 h c24 c12 c43 c20
    have c14 := r3 h c31 c03 c30
    have c42 := r3 h c14 c01 c10
    have c51 := r3 h c05 c30 c04
    have c41 := r4 h c10 c14 c03
    have c50 := r4 h c04 c03 c41
    have c45 := r4 h c51 c50 c14
    rcases cv5 (op 4 0) with c40|c40|c40|c40|c40|c40
    · exact kr h c40 c42
    · exact k1 h c40 c14 c00 c40
    · have c25 := r3 h c42 c04 c40
      exact k1 h c25 c02 c51 c24
    · exact kr h c40 c41
    · exact kr h c40 c45
    have c54 := r4 h c40 c42 c01
    exact kr h c50 c54
  · have c25 := r3 h c02 c10 c01
    rcases cv4 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c01 c20 c10 c05
    · exact kr h c20 c25
    · have c12 := r3 h c01 c20 c02
      have c21 := r4 h c12 c12 c20
      have c11 := r3 h c21 c02 c25
      exact kr h c10 c11
    · have c13 := r3 h c01 c20 c02
      rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c22 := r3 h c12 c01 c13
        exact kr h c20 c22
      · have c11 := r4 h c12 c13 c20
        exact k1 h c11 c01 c12 c11
      · exact kr h c12 c13
      · have c31 := r4 h c12 c13 c20
        rcases cv4 (op 5 1) with c51|c51|c51|c51|c51|c51
        · exact k1 h c10 c51 c00 c10
        · exact k1 h c10 c51 c01 c12
        · have c11 := r1 h c10 c51 c02
          exact k1 h c11 c01 c12 c13
        · have c14 := r1 h c10 c51 c03
          have c30 := r1 h c31 c03 c14
          exact k1 h c05 c30 c51 c03
        · exact k1 h c10 c51 c05 c13
        have c15 := r1 h c10 c51 c04
        have c30 := r4 h c05 c04 c51
        have c14 := r3 h c31 c03 c30
        exact kr h c14 c15
      · exact kr h c12 c10
      have c41 := r4 h c12 c13 c20
      rcases cv3 (op 1 5) with c15|c15|c15|c15|c15|c15
      · have c51 := r4 h c10 c15 c04
        have c40 := r1 h c41 c04 c15
        have c31 := r3 h c03 c40 c05
        have c30 := r4 h c05 c04 c51
        exact k1 h c30 c13 c02 c31
      · exact k1 h c41 c04 c15 c41
      · exact kr h c15 c13
      · exact kr h c15 c12
      · exact kr h c15 c10
      have c43 := r1 h c41 c04 c15
      rcases cv5 (op 2 1) with c21|c21|c21|c21|c21|c21
      · have c11 := r3 h c21 c02 c25
        exact kr h c10 c11
      · exact kr h c21 c25
      · have c22 := r4 h c21 c25 c10
        exact k1 h c22 c02 c21 c22
      · exact kr h c21 c20
      · have c42 := r4 h c21 c25 c10
        exact k1 h c42 c04 c25 c41
      have c54 := r3 h c25 c12 c21
      have c51 := r1 h c54 c15 c43
      exact k1 h c10 c51 c04 c15
    · have c15 := r3 h c01 c20 c02
      rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c51 := r4 h c10 c12 c01
        have c50 := r1 h c51 c15 c12
        have c21 := r1 h c25 c12 c50
        exact kr h c20 c21
      · have c51 := r3 h c25 c12 c20
        exact k1 h c10 c51 c00 c10
      · exact kr h c12 c15
      · have c31 := r4 h c12 c15 c20
        have c53 := r3 h c25 c12 c20
        have c21 := r4 h c15 c10 c53
        have c32 := r4 h c21 c25 c10
        exact kr h c31 c32
      · exact kr h c12 c10
      have c41 := r4 h c12 c15 c20
      have c54 := r3 h c25 c12 c20
      have c42 := r1 h c41 c04 c15
      have c21 := r4 h c15 c10 c54
      have c11 := r3 h c21 c42 c25
      exact kr h c10 c11
    have c14 := r3 h c01 c20 c02
    rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c22 := r3 h c12 c01 c14
      exact kr h c20 c22
    · have c11 := r4 h c12 c14 c20
      exact k1 h c11 c01 c12 c11
    · exact kr h c12 c14
    · have c31 := r4 h c12 c14 c20
      have c32 := r1 h c31 c03 c14
      rcases cv3 (op 4 2) with c42|c42|c42|c42|c42|c42
      · exact k1 h c20 c42 c00 c20
      · have c22 := r1 h c20 c42 c01
        have c40 := r1 h c42 c14 c22
        exact k1 h c03 c40 c32 c01
      · have c21 := r1 h c20 c42 c02
        have c11 := r3 h c21 c02 c25
        exact kr h c10 c11
      · exact k1 h c20 c42 c04 c25
      · have c23 := r1 h c20 c42 c05
        exact k1 h c23 c02 c31 c20
      have c50 := r4 h c04 c03 c42
      have c52 := r1 h c50 c25 c01
      have c23 := r3 h c52 c05 c50
      exact k1 h c23 c02 c31 c20
    · exact kr h c12 c10
    have c41 := r4 h c12 c14 c20
    rcases cv1 (op 4 0) with c40|c40|c40|c40|c40|c40
    · exact kr h c40 c41
    · have c24 := r4 h c40 c41 c02
      have c22 := r4 h c24 c20 c41
      exact kr h c22 c25
    · have c50 := r4 h c04 c03 c40
      have c54 := r1 h c50 c05 c03
      exact k1 h c25 c12 c54 c20
    · have c44 := r4 h c40 c41 c02
      have c21 := r4 h c14 c12 c44
      exact kr h c20 c21
    · have c54 := r4 h c40 c41 c02
      have c35 := r3 h c03 c40 c05
      have c50 := r1 h c54 c25 c41
      have c30 := r4 h c05 c04 c50
      exact k1 h c30 c03 c04 c35
    have c15 := r3 h c41 c04 c40
    have c31 := r3 h c03 c40 c05
    have c52 := r3 h c15 c01 c10
    have c51 := r4 h c10 c15 c04
    have c30 := r4 h c05 c04 c51
    have c53 := r4 h c31 c30 c15
    rcases cv3 (op 5 0) with c50|c50|c50|c50|c50|c50
    · exact kr h c50 c52
    · exact k1 h c50 c15 c00 c50
    · have c23 := r3 h c52 c05 c50
      exact k1 h c23 c02 c31 c25
    · exact kr h c50 c51
    · exact kr h c50 c53
    have c35 := r4 h c50 c52 c01
    exact kr h c30 c35
  have c23 := r3 h c02 c10 c01
  rcases cv5 (op 2 0) with c20|c20|c20|c20|c20|c20
  · exact k1 h c01 c20 c10 c03
  · exact kr h c20 c23
  · have c12 := r3 h c01 c20 c02
    have c21 := r4 h c12 c12 c20
    have c11 := r3 h c21 c02 c23
    exact kr h c10 c11
  · have c13 := r3 h c01 c20 c02
    rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c31 := r4 h c10 c12 c01
      have c30 := r1 h c31 c13 c12
      have c21 := r1 h c23 c12 c30
      exact kr h c20 c21
    · have c31 := r3 h c23 c12 c20
      exact k1 h c10 c31 c00 c10
    · exact kr h c12 c13
    · exact kr h c12 c10
    · have c41 := r4 h c12 c13 c20
      have c34 := r3 h c23 c12 c20
      have c21 := r4 h c13 c10 c34
      have c42 := r4 h c21 c23 c10
      exact kr h c41 c42
    have c51 := r4 h c12 c13 c20
    have c35 := r3 h c23 c12 c20
    have c52 := r1 h c51 c05 c13
    have c21 := r4 h c13 c10 c35
    have c11 := r3 h c21 c52 c23
    exact kr h c10 c11
  · have c14 := r3 h c01 c20 c02
    rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c22 := r3 h c12 c01 c14
      exact kr h c20 c22
    · have c11 := r4 h c12 c14 c20
      exact k1 h c11 c01 c12 c11
    · exact kr h c12 c14
    · exact kr h c12 c10
    · have c41 := r4 h c12 c14 c20
      rcases cv5 (op 3 1) with c31|c31|c31|c31|c31|c31
      · exact k1 h c10 c31 c00 c10
      · exact k1 h c10 c31 c01 c12
      · have c11 := r1 h c10 c31 c02
        exact k1 h c11 c01 c12 c14
      · exact k1 h c10 c31 c03 c14
      · have c15 := r1 h c10 c31 c04
        have c40 := r1 h c41 c04 c15
        exact k1 h c03 c40 c31 c04
      have c13 := r1 h c10 c31 c05
      have c40 := r4 h c03 c05 c31
      have c15 := r3 h c41 c04 c40
      exact kr h c13 c15
    have c51 := r4 h c12 c14 c20
    rcases cv4 (op 1 3) with c13|c13|c13|c13|c13|c13
    · have c31 := r4 h c10 c13 c05
      have c50 := r1 h c51 c05 c13
      have c40 := r4 h c03 c05 c31
      have c41 := r3 h c04 c50 c03
      exact k1 h c40 c14 c02 c41
    · exact k1 h c51 c05 c13 c51
    · exact kr h c13 c14
    · exact kr h c13 c10
    · exact kr h c13 c12
    have c54 := r1 h c51 c05 c13
    rcases cv3 (op 2 1) with c21|c21|c21|c21|c21|c21
    · have c11 := r3 h c21 c02 c23
      exact kr h c10 c11
    · exact kr h c21 c23
    · have c22 := r4 h c21 c23 c10
      exact k1 h c22 c02 c21 c22
    · exact kr h c21 c20
    · have c52 := r4 h c21 c23 c10
      exact k1 h c52 c05 c23 c51
    have c35 := r3 h c23 c12 c21
    have c31 := r1 h c35 c13 c54
    exact k1 h c10 c31 c05 c13
  have c15 := r3 h c01 c20 c02
  rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
  · have c22 := r3 h c12 c01 c15
    exact kr h c20 c22
  · have c11 := r4 h c12 c15 c20
    exact k1 h c11 c01 c12 c11
  · exact kr h c12 c15
  · exact kr h c12 c10
  · have c41 := r4 h c12 c15 c20
    have c42 := r1 h c41 c04 c15
    rcases cv2 (op 3 1) with c31|c31|c31|c31|c31|c31
    · exact k1 h c10 c31 c00 c10
    · exact k1 h c10 c31 c01 c12
    · have c14 := r1 h c10 c31 c03
      have c11 := r1 h c14 c01 c42
      exact kr h c11 c12
    · exact k1 h c10 c31 c04 c15
    · have c40 := r4 h c03 c05 c31
      exact kr h c40 c42
    have c11 := r1 h c10 c31 c02
    have c14 := r1 h c11 c01 c12
    have c30 := r1 h c31 c23 c11
    have c51 := r3 h c05 c30 c04
    have c13 := rc5 h 3 c11 c14 c15 c10 c12
    have c34 := r3 h c13 c51 c10
    exact k1 h c23 c12 c34 c20
  have c51 := r4 h c12 c15 c20
  rcases cv1 (op 5 0) with c50|c50|c50|c50|c50|c50
  · exact kr h c50 c51
  · have c25 := r4 h c50 c51 c02
    have c22 := r4 h c25 c20 c51
    exact kr h c22 c23
  · have c35 := r4 h c50 c51 c02
    have c43 := r3 h c04 c50 c03
    have c30 := r1 h c35 c23 c51
    have c40 := r4 h c03 c05 c30
    exact k1 h c40 c04 c05 c43
  · have c30 := r4 h c05 c04 c50
    have c35 := r1 h c30 c03 c04
    exact k1 h c23 c12 c35 c20
  · have c55 := r4 h c50 c51 c02
    have c21 := r4 h c15 c12 c55
    exact kr h c20 c21
  have c13 := r3 h c51 c05 c50
  have c32 := r3 h c13 c01 c10
  have c41 := r3 h c04 c50 c03
  have c31 := r4 h c10 c13 c05
  have c40 := r4 h c03 c05 c31
  have c34 := r4 h c41 c40 c13
  rcases cv4 (op 3 0) with c30|c30|c30|c30|c30|c30
  · exact kr h c30 c32
  · exact k1 h c30 c13 c00 c30
  · have c24 := r3 h c32 c03 c30
    exact k1 h c24 c02 c41 c23
  · exact kr h c30 c34
  · exact kr h c30 c31
  have c43 := r4 h c30 c32 c01
  exact kr h c40 c43

private theorem sym4 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 2) (c02 : op 0 2 = 1) (c03 : op 0 3 = 4) : False := by
  rcases cv5 (op 0 4) with c04|c04|c04|c04|c04|c04
  · exact kr h c04 c00
  · exact kr h c04 c02
  · exact kr h c04 c01
  · exact n4 h c00 c01 c02 c03 c04
  · exact kr h c04 c03
  exact n5 h c00 c01 c02 c03 c04

private theorem n6 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 2) (c02 : op 0 2 = 3) (c03 : op 0 3 = 1) (c04 : op 0 4 = 5) : False := by
  have c05 := rc4 h 5 c00 c03 c01 c02 c04
  rcases cv3 (op 4 0) with c40|c40|c40|c40|c40|c40
  · have c44 := r1 h c40 c04 c05
    exact kr h c40 c44
  · have c51 := r3 h c05 c40 c04
    rcases cv3 (op 5 0) with c50|c50|c50|c50|c50|c50
    · exact k1 h c04 c50 c40 c01
    · have c41 := r3 h c04 c50 c05
      rcases cv3 (op 4 5) with c45|c45|c45|c45|c45|c45
      · have c14 := r4 h c40 c45 c04
        have c10 := r3 h c51 c45 c50
        exact k1 h c14 c41 c45 c10
      · exact kr h c45 c40
      · have c12 := r3 h c51 c45 c50
        have c24 := r4 h c45 c41 c50
        have c54 := r4 h c41 c40 c12
        have c25 := r4 h c54 c51 c40
        exact kr h c24 c25
      · have c14 := r3 h c51 c45 c50
        exact k1 h c40 c14 c00 c40
      · exact kr h c45 c41
      have c13 := r3 h c51 c45 c50
      have c34 := r4 h c45 c41 c50
      have c54 := r4 h c41 c40 c13
      have c35 := r1 h c34 c03 c41
      have c44 := r3 h c54 c35 c51
      exact kr h c40 c44
    · have c42 := r3 h c04 c50 c05
      rcases cv3 (op 4 5) with c45|c45|c45|c45|c45|c45
      · have c55 := r3 h c45 c04 c42
        exact kr h c50 c55
      · exact kr h c45 c40
      · have c24 := r4 h c45 c42 c50
        rcases cv3 (op 1 4) with c14|c14|c14|c14|c14|c14
        · exact k1 h c40 c14 c00 c40
        · exact k1 h c40 c14 c01 c42
        · have c43 := r1 h c40 c14 c02
          have c20 := r1 h c24 c02 c43
          exact k1 h c01 c20 c14 c02
        · exact k1 h c40 c14 c04 c45
        · have c44 := r1 h c40 c14 c05
          exact k1 h c44 c04 c45 c42
        have c41 := r1 h c40 c14 c03
        have c20 := r4 h c01 c03 c14
        have c43 := r3 h c24 c02 c20
        exact kr h c41 c43
      · have c44 := r4 h c45 c42 c50
        exact k1 h c44 c04 c45 c44
      · exact kr h c45 c42
      have c34 := r4 h c45 c42 c50
      rcases cv2 (op 4 1) with c41|c41|c41|c41|c41|c41
      · have c14 := r4 h c40 c41 c03
        have c20 := r4 h c01 c03 c14
        have c30 := r1 h c34 c03 c41
        have c24 := r1 h c20 c42 c05
        exact k1 h c02 c30 c24 c00
      · exact kr h c41 c40
      · exact kr h c41 c45
      · exact k1 h c34 c03 c41 c34
      · exact kr h c41 c42
      have c32 := r1 h c34 c03 c41
      rcases cv1 (op 3 0) with c30|c30|c30|c30|c30|c30
      · exact kr h c30 c34
      · have c22 := r3 h c02 c30 c01
        have c54 := r4 h c42 c41 c22
        exact kr h c50 c54
      · have c23 := r3 h c02 c30 c01
        have c54 := r4 h c42 c41 c23
        have c35 := r4 h c54 c51 c40
        exact k1 h c35 c03 c51 c34
      · exact kr h c30 c32
      · have c25 := r3 h c02 c30 c01
        have c54 := r4 h c42 c41 c25
        have c55 := r4 h c54 c51 c40
        exact k1 h c55 c05 c54 c55
      have c13 := r4 h c30 c34 c05
      have c55 := r1 h c51 c45 c13
      have c21 := r3 h c02 c30 c01
      have c54 := r4 h c42 c41 c21
      have c15 := r4 h c54 c51 c40
      have c52 := r3 h c15 c01 c13
      exact k1 h c55 c15 c50 c52
    · exact kr h c50 c51
    · have c45 := r3 h c04 c50 c05
      have c54 := r4 h c45 c45 c50
      have c44 := r3 h c54 c05 c51
      exact kr h c40 c44
    have c43 := r3 h c04 c50 c05
    rcases cv3 (op 4 5) with c45|c45|c45|c45|c45|c45
    · have c55 := r3 h c45 c04 c43
      exact kr h c50 c55
    · exact kr h c45 c40
    · have c24 := r4 h c45 c43 c50
      have c25 := r1 h c24 c02 c43
      rcases cv5 (op 1 4) with c14|c14|c14|c14|c14|c14
      · exact k1 h c40 c14 c00 c40
      · have c42 := r1 h c40 c14 c01
        have c44 := r1 h c42 c04 c25
        exact kr h c44 c45
      · exact k1 h c40 c14 c02 c43
      · have c20 := r4 h c01 c03 c14
        exact kr h c20 c25
      · exact k1 h c40 c14 c04 c45
      have c44 := r1 h c40 c14 c05
      have c10 := r1 h c14 c51 c44
      have c42 := r1 h c44 c04 c45
      have c41 := rc3 h 1 c44 c40 c45 c42 c43
      have c11 := r1 h c10 c41 c03
      have c34 := r4 h c41 c40 c11
      exact k1 h c03 c10 c34 c01
    · have c44 := r4 h c45 c43 c50
      exact k1 h c44 c04 c45 c44
    · exact kr h c45 c43
    have c34 := r4 h c45 c43 c50
    rcases cv4 (op 3 0) with c30|c30|c30|c30|c30|c30
    · exact kr h c30 c34
    · have c13 := r4 h c30 c34 c05
      have c21 := r3 h c02 c30 c01
      have c10 := r1 h c13 c51 c34
      have c20 := r4 h c01 c03 c10
      exact k1 h c20 c02 c03 c21
    · have c10 := r4 h c03 c02 c30
      have c13 := r1 h c10 c01 c02
      exact k1 h c51 c45 c13 c50
    · have c33 := r4 h c30 c34 c05
      have c54 := r4 h c43 c45 c33
      have c35 := r4 h c54 c51 c40
      exact k1 h c35 c03 c51 c34
    · have c53 := r4 h c30 c34 c05
      have c55 := r4 h c53 c50 c34
      exact k1 h c55 c45 c53 c55
    have c24 := r3 h c02 c30 c01
    have c41 := r3 h c34 c03 c30
    have c14 := r4 h c40 c41 c03
    have c20 := r4 h c01 c03 c14
    have c15 := r3 h c41 c04 c40
    have c12 := r4 h c24 c20 c41
    rcases cv5 (op 1 0) with c10|c10|c10|c10|c10|c10
    · exact kr h c10 c15
    · exact kr h c10 c12
    · have c21 := r4 h c10 c15 c04
      exact kr h c20 c21
    · exact kr h c10 c14
    · exact k1 h c10 c41 c00 c10
    have c52 := r3 h c15 c01 c10
    exact k1 h c52 c05 c24 c51
  · have c52 := r3 h c05 c40 c04
    rcases cv1 (op 5 0) with c50|c50|c50|c50|c50|c50
    · exact k1 h c04 c50 c40 c02
    · have c42 := r3 h c04 c50 c05
      rcases cv1 (op 4 5) with c45|c45|c45|c45|c45|c45
      · have c24 := r4 h c40 c45 c04
        have c20 := r3 h c52 c45 c50
        exact k1 h c24 c42 c45 c20
      · exact kr h c45 c40
      · have c23 := r3 h c52 c45 c50
        have c34 := r4 h c45 c42 c50
        have c54 := r4 h c42 c40 c23
        have c35 := r4 h c54 c52 c40
        exact kr h c34 c35
      · have c24 := r3 h c52 c45 c50
        exact k1 h c40 c24 c00 c40
      · exact kr h c45 c42
      have c21 := r3 h c52 c45 c50
      have c14 := r4 h c45 c42 c50
      have c54 := r4 h c42 c40 c21
      have c15 := r1 h c14 c01 c42
      have c44 := r3 h c54 c15 c52
      exact kr h c40 c44
    · have c43 := r3 h c04 c50 c05
      rcases cv1 (op 4 5) with c45|c45|c45|c45|c45|c45
      · have c55 := r3 h c45 c04 c43
        exact kr h c50 c55
      · exact kr h c45 c40
      · have c34 := r4 h c45 c43 c50
        rcases cv1 (op 2 4) with c24|c24|c24|c24|c24|c24
        · exact k1 h c40 c24 c00 c40
        · exact k1 h c40 c24 c02 c43
        · have c41 := r1 h c40 c24 c03
          have c30 := r1 h c34 c03 c41
          exact k1 h c02 c30 c24 c03
        · exact k1 h c40 c24 c04 c45
        · have c44 := r1 h c40 c24 c05
          exact k1 h c44 c04 c45 c43
        have c42 := r1 h c40 c24 c01
        have c30 := r4 h c02 c01 c24
        have c41 := r3 h c34 c03 c30
        exact kr h c41 c42
      · have c44 := r4 h c45 c43 c50
        exact k1 h c44 c04 c45 c44
      · exact kr h c45 c43
      have c14 := r4 h c45 c43 c50
      rcases cv3 (op 4 2) with c42|c42|c42|c42|c42|c42
      · have c24 := r4 h c40 c42 c01
        have c30 := r4 h c02 c01 c24
        have c10 := r1 h c14 c01 c42
        have c34 := r1 h c30 c43 c05
        exact k1 h c03 c10 c34 c00
      · exact kr h c42 c45
      · exact kr h c42 c40
      · exact k1 h c14 c01 c42 c14
      · exact kr h c42 c43
      have c13 := r1 h c14 c01 c42
      rcases cv2 (op 1 0) with c10|c10|c10|c10|c10|c10
      · exact kr h c10 c14
      · have c11 := r4 h c10 c14 c05
        have c51 := r4 h c11 c10 c14
        have c55 := r1 h c51 c45 c11
        have c31 := r3 h c03 c10 c02
        have c54 := r4 h c43 c42 c31
        have c15 := r4 h c54 c51 c45
        exact k1 h c55 c15 c55 c51
      · have c20 := r4 h c01 c03 c10
        have c34 := r4 h c42 c40 c20
        have c41 := r4 h c13 c10 c34
        exact k1 h c34 c03 c41 c34
      · exact kr h c10 c13
      · have c35 := r3 h c03 c10 c02
        have c54 := r4 h c43 c42 c35
        have c55 := r4 h c54 c52 c40
        exact k1 h c55 c05 c54 c55
      have c21 := r4 h c10 c14 c05
      have c55 := r1 h c52 c45 c21
      have c32 := r3 h c03 c10 c02
      have c54 := r4 h c43 c42 c32
      have c25 := r4 h c54 c52 c40
      have c53 := r3 h c25 c02 c21
      exact k1 h c55 c25 c50 c53
    · exact kr h c50 c52
    · have c45 := r3 h c04 c50 c05
      have c54 := r4 h c45 c45 c50
      have c44 := r3 h c54 c05 c52
      exact kr h c40 c44
    have c41 := r3 h c04 c50 c05
    rcases cv1 (op 4 5) with c45|c45|c45|c45|c45|c45
    · have c55 := r3 h c45 c04 c41
      exact kr h c50 c55
    · exact kr h c45 c40
    · have c34 := r4 h c45 c41 c50
      have c35 := r1 h c34 c03 c41
      rcases cv3 (op 1 5) with c15|c15|c15|c15|c15|c15
      · exact k1 h c50 c15 c00 c50
      · exact k1 h c50 c15 c01 c52
      · have c53 := r1 h c50 c15 c02
        exact k1 h c53 c05 c34 c50
      · have c55 := r1 h c50 c15 c04
        have c10 := r1 h c15 c41 c55
        exact k1 h c03 c10 c35 c04
      · have c54 := r1 h c50 c15 c05
        have c44 := r3 h c54 c05 c52
        exact kr h c40 c44
      have c51 := r1 h c50 c15 c03
      have c20 := r4 h c01 c03 c15
      have c25 := r1 h c20 c52 c04
      have c53 := r3 h c25 c02 c20
      exact kr h c51 c53
    · have c44 := r4 h c45 c41 c50
      exact k1 h c44 c04 c45 c44
    · exact kr h c45 c41
    have c14 := r4 h c45 c41 c50
    rcases cv4 (op 1 0) with c10|c10|c10|c10|c10|c10
    · exact kr h c10 c14
    · have c11 := r4 h c10 c14 c05
      have c51 := r4 h c11 c10 c14
      have c54 := r4 h c41 c45 c11
      have c55 := r1 h c51 c45 c11
      have c15 := r4 h c54 c51 c45
      exact k1 h c55 c15 c55 c51
    · have c21 := r4 h c10 c14 c05
      have c20 := r1 h c21 c52 c14
      have c30 := r4 h c02 c01 c20
      have c32 := r3 h c03 c10 c02
      exact k1 h c30 c03 c01 c32
    · have c20 := r4 h c01 c03 c10
      have c21 := r1 h c20 c02 c03
      exact k1 h c52 c45 c21 c50
    · have c51 := r4 h c10 c14 c05
      have c55 := r4 h c51 c50 c14
      exact k1 h c55 c45 c51 c55
    have c34 := r3 h c03 c10 c02
    have c42 := r3 h c14 c01 c10
    have c24 := r4 h c40 c42 c01
    have c30 := r4 h c02 c01 c24
    have c25 := r3 h c42 c04 c40
    have c23 := r4 h c34 c30 c42
    rcases cv5 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact kr h c20 c25
    · exact kr h c20 c24
    · exact kr h c20 c23
    · have c32 := r4 h c20 c25 c04
      exact kr h c30 c32
    · exact k1 h c20 c42 c00 c20
    have c53 := r3 h c25 c02 c20
    exact k1 h c53 c05 c34 c52
  · have c54 := r3 h c05 c40 c04
    have c45 := r4 h c54 c54 c40
    have c44 := r4 h c40 c45 c04
    exact kr h c40 c44
  · have c50 := r4 h c04 c05 c40
    have c55 := r3 h c05 c40 c04
    exact k1 h c50 c05 c04 c55
  have c53 := r3 h c05 c40 c04
  rcases cv2 (op 5 0) with c50|c50|c50|c50|c50|c50
  · exact k1 h c04 c50 c40 c03
  · have c41 := r3 h c04 c50 c05
    rcases cv2 (op 4 5) with c45|c45|c45|c45|c45|c45
    · have c55 := r3 h c45 c04 c41
      exact kr h c50 c55
    · have c14 := r4 h c45 c41 c50
      rcases cv2 (op 3 4) with c34|c34|c34|c34|c34|c34
      · exact k1 h c40 c34 c00 c40
      · have c42 := r1 h c40 c34 c01
        have c10 := r1 h c14 c01 c42
        exact k1 h c03 c10 c34 c01
      · exact k1 h c40 c34 c03 c41
      · exact k1 h c40 c34 c04 c45
      · have c44 := r1 h c40 c34 c05
        exact k1 h c44 c04 c45 c41
      have c43 := r1 h c40 c34 c02
      have c10 := r4 h c03 c02 c34
      have c42 := r3 h c14 c01 c10
      exact kr h c42 c43
    · exact kr h c45 c40
    · have c44 := r4 h c45 c41 c50
      exact k1 h c44 c04 c45 c44
    · exact kr h c45 c41
    have c24 := r4 h c45 c41 c50
    rcases cv1 (op 4 3) with c43|c43|c43|c43|c43|c43
    · have c34 := r4 h c40 c43 c02
      have c10 := r4 h c03 c02 c34
      have c20 := r1 h c24 c02 c43
      have c14 := r1 h c10 c41 c05
      exact k1 h c01 c20 c14 c00
    · exact kr h c43 c45
    · exact kr h c43 c40
    · exact k1 h c24 c02 c43 c24
    · exact kr h c43 c41
    have c21 := r1 h c24 c02 c43
    rcases cv3 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact kr h c20 c24
    · have c11 := r3 h c01 c20 c03
      have c54 := r4 h c41 c43 c11
      have c30 := r4 h c02 c01 c20
      have c14 := r4 h c43 c40 c30
      have c15 := r4 h c54 c53 c40
      exact kr h c14 c15
    · have c22 := r4 h c20 c24 c05
      have c12 := r3 h c01 c20 c03
      have c54 := r4 h c41 c43 c12
      have c52 := r4 h c22 c20 c24
      have c55 := r1 h c52 c45 c22
      have c25 := r4 h c54 c52 c45
      exact k1 h c55 c25 c55 c52
    · exact kr h c20 c21
    · have c15 := r3 h c01 c20 c03
      have c54 := r4 h c41 c43 c15
      have c55 := r4 h c54 c53 c40
      exact k1 h c55 c05 c54 c55
    have c32 := r4 h c20 c24 c05
    have c13 := r3 h c01 c20 c03
    have c54 := r4 h c41 c43 c13
    have c55 := r1 h c53 c45 c32
    have c35 := r4 h c54 c53 c40
    have c51 := r3 h c35 c03 c32
    exact k1 h c55 c35 c50 c51
  · have c43 := r3 h c04 c50 c05
    rcases cv2 (op 4 5) with c45|c45|c45|c45|c45|c45
    · have c34 := r4 h c40 c45 c04
      have c30 := r3 h c53 c45 c50
      exact k1 h c34 c43 c45 c30
    · have c31 := r3 h c53 c45 c50
      have c14 := r4 h c45 c43 c50
      have c54 := r4 h c43 c40 c31
      have c15 := r4 h c54 c53 c40
      exact kr h c14 c15
    · exact kr h c45 c40
    · have c34 := r3 h c53 c45 c50
      exact k1 h c40 c34 c00 c40
    · exact kr h c45 c43
    have c32 := r3 h c53 c45 c50
    have c24 := r4 h c45 c43 c50
    have c54 := r4 h c43 c40 c32
    have c25 := r1 h c24 c02 c43
    have c44 := r3 h c54 c25 c53
    exact kr h c40 c44
  · exact kr h c50 c53
  · have c45 := r3 h c04 c50 c05
    have c54 := r4 h c45 c45 c50
    have c44 := r3 h c54 c05 c53
    exact kr h c40 c44
  have c42 := r3 h c04 c50 c05
  rcases cv2 (op 4 5) with c45|c45|c45|c45|c45|c45
  · have c55 := r3 h c45 c04 c42
    exact kr h c50 c55
  · have c14 := r4 h c45 c42 c50
    have c15 := r1 h c14 c01 c42
    rcases cv1 (op 2 5) with c25|c25|c25|c25|c25|c25
    · exact k1 h c50 c25 c00 c50
    · exact k1 h c50 c25 c02 c53
    · have c51 := r1 h c50 c25 c03
      exact k1 h c51 c05 c14 c50
    · have c55 := r1 h c50 c25 c04
      have c20 := r1 h c25 c42 c55
      exact k1 h c01 c20 c15 c04
    · have c54 := r1 h c50 c25 c05
      have c44 := r3 h c54 c05 c53
      exact kr h c40 c44
    have c52 := r1 h c50 c25 c01
    have c30 := r4 h c02 c01 c25
    have c35 := r1 h c30 c53 c04
    have c51 := r3 h c35 c03 c30
    exact kr h c51 c52
  · exact kr h c45 c40
  · have c44 := r4 h c45 c42 c50
    exact k1 h c44 c04 c45 c44
  · exact kr h c45 c42
  have c24 := r4 h c45 c42 c50
  rcases cv4 (op 2 0) with c20|c20|c20|c20|c20|c20
  · exact kr h c20 c24
  · have c30 := r4 h c02 c01 c20
    have c32 := r1 h c30 c03 c01
    exact k1 h c53 c45 c32 c50
  · have c22 := r4 h c20 c24 c05
    have c52 := r4 h c22 c20 c24
    have c54 := r4 h c42 c45 c22
    have c55 := r1 h c52 c45 c22
    have c25 := r4 h c54 c52 c45
    exact k1 h c55 c25 c55 c52
  · have c32 := r4 h c20 c24 c05
    have c13 := r3 h c01 c20 c03
    have c30 := r1 h c32 c53 c24
    have c10 := r4 h c03 c02 c30
    exact k1 h c10 c01 c02 c13
  · have c52 := r4 h c20 c24 c05
    have c55 := r4 h c52 c50 c24
    exact k1 h c55 c45 c52 c55
  have c14 := r3 h c01 c20 c03
  have c43 := r3 h c24 c02 c20
  have c34 := r4 h c40 c43 c02
  have c10 := r4 h c03 c02 c34
  have c35 := r3 h c43 c04 c40
  have c31 := r4 h c14 c10 c43
  rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
  · exact kr h c30 c35
  · have c13 := r4 h c30 c35 c04
    exact kr h c10 c13
  · exact kr h c30 c34
  · exact kr h c30 c31
  · exact k1 h c30 c43 c00 c30
  have c51 := r3 h c35 c03 c30
  exact k1 h c51 c05 c14 c53

private theorem n7 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 2) (c02 : op 0 2 = 3) (c03 : op 0 3 = 4) (c04 : op 0 4 = 1) : False := by
  have c05 := rc5 h 5 c00 c04 c01 c02 c03
  rcases cv2 (op 1 0) with c10|c10|c10|c10|c10|c10
  · have c13 := r1 h c10 c01 c02
    exact kr h c10 c13
  · have c41 := r3 h c04 c10 c03
    rcases cv2 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c10 c11 c00 c10
    · exact kr h c11 c10
    · have c14 := r1 h c10 c11 c03
      have c31 := r4 h c11 c10 c14
      rcases cv5 (op 4 2) with c42|c42|c42|c42|c42|c42
      · exact k1 h c14 c01 c42 c10
      · exact k1 h c14 c01 c42 c11
      · have c12 := r1 h c14 c01 c42
        have c20 := r4 h c01 c04 c12
        have c24 := r4 h c42 c42 c20
        have c22 := r4 h c20 c24 c03
        have c32 := r4 h c22 c20 c24
        exact kr h c31 c32
      · exact kr h c42 c41
      · exact k1 h c14 c01 c42 c14
      have c15 := r1 h c14 c01 c42
      have c20 := r4 h c01 c04 c15
      rcases cv2 (op 4 3) with c43|c43|c43|c43|c43|c43
      · exact k1 h c31 c43 c10 c31
      · have c34 := r4 h c41 c43 c11
        have c13 := r4 h c34 c31 c43
        exact kr h c11 c13
      · exact kr h c43 c41
      · have c30 := r1 h c31 c43 c14
        have c21 := r3 h c02 c30 c01
        have c12 := r4 h c21 c21 c10
        exact kr h c12 c14
      · exact kr h c43 c42
      rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact kr h c12 c14
      · exact kr h c12 c10
      · have c32 := r1 h c31 c43 c12
        have c24 := r4 h c43 c41 c32
        have c21 := r4 h c12 c12 c24
        exact k1 h c21 c42 c15 c24
      · exact kr h c12 c11
      · exact kr h c12 c15
      have c13 := rc2 h 3 c14 c10 c11 c15 c12
      have c35 := r1 h c31 c43 c12
      have c21 := r4 h c13 c11 c35
      exact kr h c20 c21
    · exact k1 h c10 c11 c04 c11
    · have c15 := r1 h c10 c11 c05
      have c51 := r4 h c11 c10 c15
      have c50 := r4 h c05 c05 c51
      have c52 := r3 h c15 c01 c11
      exact kr h c50 c52
    have c13 := r1 h c10 c11 c02
    have c21 := r4 h c11 c10 c13
    rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
    · exact kr h c12 c13
    · exact kr h c12 c10
    · exact kr h c12 c11
    · have c32 := r3 h c13 c01 c12
      have c23 := r1 h c21 c32 c12
      have c31 := r4 h c12 c11 c23
      have c33 := r1 h c32 c23 c21
      exact k1 h c33 c23 c31 c33
    · have c20 := r4 h c01 c04 c12
      have c23 := r3 h c12 c41 c11
      rcases cv5 (op 2 2) with c22|c22|c22|c22|c22|c22
      · exact k1 h c20 c22 c00 c20
      · exact kr h c22 c23
      · exact kr h c22 c20
      · exact kr h c22 c21
      · exact k1 h c20 c22 c04 c21
      have c25 := r1 h c20 c22 c05
      have c52 := r4 h c22 c20 c25
      have c50 := r4 h c05 c05 c52
      have c53 := r3 h c25 c02 c22
      exact kr h c50 c53
    rcases cv3 (op 1 4) with c14|c14|c14|c14|c14|c14
    · exact kr h c14 c13
    · exact kr h c14 c10
    · exact kr h c14 c11
    · have c15 := rc3 h 5 c13 c10 c11 c14 c12
      have c32 := r3 h c13 c01 c15
      have c43 := r3 h c14 c41 c14
      have c23 := r1 h c21 c32 c15
      have c35 := r3 h c23 c12 c21
      have c44 := r4 h c43 c41 c35
      have c54 := r4 h c44 c43 c41
      exact k1 h c54 c15 c43 c54
    · exact kr h c14 c12
    have c15 := rc4 h 5 c13 c10 c11 c14 c12
    have c20 := r4 h c01 c04 c15
    have c32 := r3 h c13 c01 c14
    have c53 := r3 h c15 c41 c12
    have c23 := r1 h c21 c32 c14
    have c51 := r4 h c12 c11 c23
    have c35 := r3 h c23 c12 c21
    have c25 := r4 h c53 c51 c35
    exact kr h c20 c25
  · have c43 := r3 h c04 c10 c03
    rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
    · have c31 := r1 h c30 c03 c04
      exact kr h c30 c31
    · have c21 := r3 h c02 c30 c01
      rcases cv5 (op 1 1) with c11|c11|c11|c11|c11|c11
      · have c31 := r4 h c10 c11 c04
        have c13 := r3 h c31 c43 c30
        exact kr h c11 c13
      · have c12 := r4 h c21 c21 c11
        exact k1 h c12 c11 c21 c11
      · have c12 := r1 h c11 c21 c11
        have c22 := r1 h c21 c12 c11
        exact k1 h c22 c12 c21 c21
      · exact kr h c11 c10
      · have c20 := r4 h c01 c04 c11
        exact kr h c20 c21
      rcases cv4 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact k1 h c30 c13 c00 c30
      · have c12 := r4 h c21 c21 c13
        exact kr h c10 c12
      · have c33 := r1 h c30 c13 c02
        have c31 := r3 h c13 c21 c10
        exact kr h c31 c33
      · exact kr h c13 c10
      · exact kr h c13 c11
      have c31 := r1 h c30 c13 c04
      have c14 := r3 h c31 c03 c30
      have c42 := r3 h c14 c01 c13
      exact kr h c42 c43
    · have c40 := r4 h c03 c02 c30
      have c42 := r1 h c40 c04 c01
      exact kr h c40 c42
    · have c34 := r4 h c43 c43 c30
      have c33 := r4 h c30 c34 c03
      exact kr h c30 c33
    · have c34 := r1 h c30 c43 c03
      have c44 := r1 h c43 c34 c30
      have c33 := r1 h c34 c03 c44
      exact kr h c30 c33
    have c25 := r3 h c02 c30 c01
    rcases cv0 (op 3 3) with c33|c33|c33|c33|c33|c33
    · rcases cv2 (op 3 1) with c31|c31|c31|c31|c31|c31
      · exact k1 h c10 c31 c00 c10
      · exact kr h c31 c33
      · have c13 := r4 h c33 c31 c33
        have c34 := r4 h c43 c43 c31
        exact k1 h c34 c13 c43 c33
      · have c13 := r3 h c31 c43 c33
        exact k1 h c33 c13 c33 c31
      · exact kr h c31 c30
      have c13 := r1 h c10 c31 c02
      have c35 := r1 h c33 c13 c30
      have c34 := r4 h c43 c43 c35
      exact kr h c30 c34
    · have c40 := r4 h c03 c02 c33
      exact kr h c40 c43
    · have c34 := r4 h c43 c43 c33
      exact k1 h c34 c33 c43 c33
    · have c34 := r1 h c33 c43 c33
      have c44 := r1 h c43 c34 c33
      exact k1 h c44 c34 c43 c43
    · exact kr h c33 c30
    have c53 := r4 h c30 c33 c02
    rcases cv2 (op 3 4) with c34|c34|c34|c34|c34|c34
    · exact kr h c34 c33
    · have c31 := r1 h c33 c03 c34
      exact k1 h c53 c25 c31 c53
    · exact k1 h c33 c03 c34 c33
    · exact k1 h c33 c03 c34 c34
    · exact kr h c34 c30
    have c40 := r4 h c03 c02 c34
    have c32 := r1 h c33 c03 c34
    have c20 := r3 h c32 c33 c34
    have c14 := r3 h c01 c20 c04
    have c41 := r4 h c14 c14 c40
    have c44 := r4 h c40 c41 c04
    exact kr h c40 c44
  · have c20 := r4 h c01 c04 c10
    have c24 := r1 h c20 c02 c03
    exact kr h c20 c24
  · have c45 := r3 h c04 c10 c03
    rcases cv2 (op 5 0) with c50|c50|c50|c50|c50|c50
    · exact k1 h c05 c50 c50 c00
    · have c51 := r3 h c05 c50 c05
      have c15 := r1 h c10 c51 c05
      exact k1 h c50 c15 c00 c50
    · have c53 := r3 h c05 c50 c05
      rcases cv1 (op 5 5) with c55|c55|c55|c55|c55|c55
      · have c35 := r4 h c50 c55 c05
        have c30 := r3 h c53 c55 c50
        exact k1 h c35 c53 c55 c30
      · have c25 := r4 h c55 c53 c50
        exact k1 h c25 c02 c53 c25
      · exact kr h c55 c50
      · exact k1 h c55 c45 c53 c55
      · exact kr h c55 c53
      have c15 := r4 h c55 c53 c50
      have c51 := r4 h c10 c15 c05
      have c11 := r3 h c51 c55 c55
      exact kr h c10 c11
    · have c54 := r1 h c50 c45 c03
      exact k1 h c05 c50 c54 c00
    · have c55 := r3 h c05 c50 c05
      exact kr h c50 c55
    have c52 := r3 h c05 c50 c05
    rcases cv3 (op 5 5) with c55|c55|c55|c55|c55|c55
    · have c25 := r4 h c50 c55 c05
      have c20 := r3 h c52 c55 c50
      exact k1 h c25 c52 c55 c20
    · have c15 := r4 h c55 c52 c50
      exact k1 h c15 c01 c52 c15
    · exact kr h c55 c50
    · have c53 := r3 h c55 c45 c52
      exact kr h c50 c53
    · exact kr h c55 c52
    have c23 := r3 h c52 c55 c50
    have c35 := r4 h c55 c52 c50
    rcases cv3 (op 2 5) with c25|c25|c25|c25|c25|c25
    · exact kr h c25 c23
    · exact k1 h c50 c25 c01 c52
    · have c53 := r1 h c50 c25 c02
      exact k1 h c53 c05 c35 c50
    · have c51 := r1 h c50 c25 c04
      exact k1 h c10 c51 c00 c10
    · exact k1 h c50 c25 c05 c55
    have c54 := r1 h c50 c25 c03
    have c33 := r3 h c23 c02 c25
    have c30 := r1 h c35 c03 c54
    exact kr h c30 c33
  have c42 := r3 h c04 c10 c03
  rcases cv3 (op 1 4) with c14|c14|c14|c14|c14|c14
  · have c21 := r4 h c10 c14 c03
    have c13 := r1 h c14 c01 c42
    have c20 := r4 h c01 c04 c13
    exact kr h c20 c21
  · rcases cv5 (op 1 1) with c11|c11|c11|c11|c11|c11
    · have c12 := r3 h c11 c01 c14
      have c40 := r3 h c14 c11 c12
      have c20 := r4 h c01 c04 c12
      have c32 := r3 h c03 c40 c02
      have c23 := r4 h c32 c32 c20
      have c22 := r4 h c20 c23 c02
      exact kr h c20 c22
    · exact kr h c11 c14
    · exact kr h c11 c10
    · rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c21 := r4 h c10 c12 c01
        have c22 := r1 h c21 c12 c10
        exact k1 h c12 c01 c22 c11
      · exact kr h c12 c14
      · exact kr h c12 c10
      · exact kr h c12 c11
      · have c31 := r4 h c11 c14 c12
        have c40 := r4 h c03 c02 c31
        exact k1 h c40 c14 c01 c42
      rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact kr h c13 c14
      · exact kr h c13 c10
      · exact kr h c13 c11
      · have c43 := r3 h c14 c11 c13
        exact kr h c42 c43
      · exact kr h c13 c12
      have c15 := rc4 h 5 c13 c14 c10 c11 c12
      have c20 := r4 h c01 c04 c15
      have c32 := r3 h c13 c01 c11
      have c43 := r3 h c14 c11 c15
      have c35 := r1 h c32 c13 c20
      have c40 := r4 h c03 c02 c35
      exact kr h c40 c43
    · have c41 := r4 h c11 c14 c11
      have c44 := r1 h c41 c14 c11
      exact k1 h c44 c14 c41 c41
    rcases cv3 (op 1 5) with c15|c15|c15|c15|c15|c15
    · have c21 := r4 h c10 c15 c05
      have c52 := r3 h c15 c01 c11
      have c25 := r1 h c21 c52 c11
      have c12 := r4 h c25 c21 c52
      exact kr h c10 c12
    · exact kr h c15 c14
    · exact kr h c15 c10
    · have c51 := r4 h c11 c14 c15
      have c45 := r3 h c14 c11 c15
      have c50 := r4 h c05 c05 c51
      have c54 := r4 h c45 c45 c51
      exact kr h c50 c54
    · exact kr h c15 c11
    rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c21 := r4 h c10 c12 c01
      have c22 := r1 h c21 c12 c10
      exact k1 h c12 c01 c22 c11
    · exact kr h c12 c14
    · exact kr h c12 c10
    · exact kr h c12 c15
    · exact kr h c12 c11
    have c13 := rc0 h 3 c14 c10 c15 c12 c11
    have c21 := r4 h c10 c13 c02
    have c20 := r4 h c01 c04 c12
    exact kr h c20 c21
  · exact kr h c14 c10
  · have c20 := r4 h c01 c04 c14
    have c24 := r1 h c20 c42 c03
    have c43 := r3 h c24 c02 c20
    have c31 := r3 h c43 c04 c42
    have c40 := r4 h c03 c02 c31
    have c41 := r1 h c40 c14 c04
    have c11 := r3 h c41 c04 c40
    exact k1 h c14 c41 c40 c11
  · rcases cv1 (op 1 1) with c11|c11|c11|c11|c11|c11
    · have c21 := r4 h c10 c11 c04
      rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact kr h c12 c11
      · exact k1 h c11 c01 c12 c11
      · exact kr h c12 c10
      · exact k1 h c11 c01 c12 c14
      · exact kr h c12 c14
      have c13 := r1 h c11 c01 c12
      exact k1 h c21 c42 c13 c21
    · exact kr h c11 c10
    · rcases cv1 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c21 := r4 h c10 c12 c01
        have c22 := r1 h c21 c12 c10
        exact k1 h c12 c01 c22 c11
      · exact kr h c12 c10
      · exact kr h c12 c11
      · have c20 := r4 h c01 c04 c12
        rcases cv1 (op 1 3) with c13|c13|c13|c13|c13|c13
        · have c21 := r4 h c10 c13 c02
          exact kr h c20 c21
        · exact kr h c13 c10
        · exact kr h c13 c11
        · exact kr h c13 c12
        · exact kr h c13 c14
        have c31 := r4 h c11 c13 c11
        have c33 := r1 h c31 c13 c11
        exact k1 h c33 c13 c31 c31
      · exact kr h c12 c14
      have c31 := r4 h c11 c12 c10
      have c35 := r1 h c31 c03 c14
      have c23 := r3 h c12 c11 c10
      rcases cv4 (op 1 3) with c13|c13|c13|c13|c13|c13
      · have c32 := r3 h c13 c01 c11
        exact kr h c32 c35
      · exact kr h c13 c12
      · exact kr h c13 c10
      · exact kr h c13 c11
      · exact kr h c13 c14
      have c20 := r4 h c01 c04 c13
      have c33 := r3 h c23 c02 c20
      exact kr h c31 c33
    · have c20 := r4 h c01 c04 c11
      have c30 := r4 h c02 c01 c20
      have c31 := r1 h c30 c03 c04
      exact kr h c30 c31
    · exact kr h c11 c14
    rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c21 := r4 h c10 c12 c01
      have c22 := r1 h c21 c12 c10
      exact k1 h c12 c01 c22 c11
    · exact kr h c12 c11
    · exact kr h c12 c10
    · rcases cv4 (op 1 3) with c13|c13|c13|c13|c13|c13
      · have c21 := r4 h c10 c13 c02
        have c32 := r3 h c13 c01 c12
        have c23 := r4 h c32 c32 c21
        have c22 := r4 h c21 c23 c12
        exact kr h c21 c22
      · exact kr h c13 c11
      · exact kr h c13 c10
      · exact kr h c13 c12
      · exact kr h c13 c14
      have c15 := rc0 h 5 c11 c10 c12 c13 c14
      have c21 := r4 h c10 c15 c05
      have c51 := r4 h c14 c13 c42
      have c52 := r3 h c15 c01 c14
      have c25 := r1 h c21 c52 c14
      exact k1 h c51 c25 c11 c51
    · exact kr h c12 c14
    have c20 := r4 h c01 c04 c12
    rcases cv3 (op 1 3) with c13|c13|c13|c13|c13|c13
    · have c21 := r4 h c10 c13 c02
      exact kr h c20 c21
    · exact kr h c13 c11
    · exact kr h c13 c10
    · exact kr h c13 c12
    · exact kr h c13 c14
    have c15 := rc0 h 5 c11 c10 c13 c12 c14
    have c21 := r4 h c10 c15 c05
    have c52 := r3 h c15 c01 c14
    have c25 := r1 h c21 c52 c14
    have c54 := r3 h c25 c12 c21
    have c40 := r3 h c54 c15 c52
    have c51 := r4 h c14 c12 c40
    have c50 := r1 h c51 c05 c15
    exact k1 h c05 c50 c51 c00
  rcases cv1 (op 1 1) with c11|c11|c11|c11|c11|c11
  · have c21 := r4 h c10 c11 c04
    rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
    · exact kr h c12 c11
    · exact k1 h c11 c01 c12 c11
    · exact kr h c12 c10
    · exact kr h c12 c14
    · exact k1 h c11 c01 c12 c14
    have c15 := r1 h c11 c01 c12
    have c13 := rc4 h 3 c11 c15 c10 c14 c12
    have c24 := r1 h c21 c42 c13
    have c30 := r4 h c02 c01 c24
    have c41 := r4 h c13 c14 c30
    have c45 := r3 h c24 c12 c21
    have c40 := r1 h c41 c04 c11
    exact kr h c40 c45
  · exact kr h c11 c10
  · exact kr h c11 c14
  · have c20 := r4 h c01 c04 c11
    have c30 := r4 h c02 c01 c20
    have c31 := r1 h c30 c03 c04
    exact kr h c30 c31
  · rcases cv4 (op 1 5) with c15|c15|c15|c15|c15|c15
    · have c21 := r4 h c10 c15 c05
      have c52 := r3 h c15 c01 c11
      have c25 := r1 h c21 c52 c11
      have c12 := r4 h c25 c21 c52
      exact kr h c10 c12
    · have c51 := r4 h c11 c15 c11
      have c55 := r1 h c51 c15 c11
      exact k1 h c55 c15 c51 c51
    · exact kr h c15 c10
    · exact kr h c15 c14
    · exact kr h c15 c11
    have c20 := r4 h c01 c04 c15
    rcases cv1 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c21 := r4 h c10 c12 c01
      have c22 := r1 h c21 c12 c10
      exact k1 h c12 c01 c22 c11
    · exact kr h c12 c10
    · exact kr h c12 c14
    · exact kr h c12 c15
    · exact kr h c12 c11
    have c51 := r4 h c11 c12 c10
    have c25 := r3 h c12 c11 c10
    have c53 := r3 h c25 c02 c20
    exact kr h c51 c53
  rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
  · have c21 := r4 h c10 c12 c01
    have c22 := r1 h c21 c12 c10
    exact k1 h c12 c01 c22 c11
  · exact kr h c12 c11
  · exact kr h c12 c10
  · exact kr h c12 c14
  · have c20 := r4 h c01 c04 c12
    rcases cv5 (op 1 3) with c13|c13|c13|c13|c13|c13
    · have c21 := r4 h c10 c13 c02
      exact kr h c20 c21
    · exact kr h c13 c11
    · exact kr h c13 c10
    · exact kr h c13 c14
    · exact kr h c13 c12
    have c15 := rc0 h 5 c11 c10 c14 c12 c13
    have c21 := r4 h c10 c15 c05
    have c52 := r3 h c15 c01 c13
    have c25 := r1 h c21 c52 c13
    rcases cv3 (op 2 2) with c22|c22|c22|c22|c22|c22
    · exact k1 h c20 c22 c00 c20
    · exact kr h c22 c25
    · exact kr h c22 c20
    · exact k1 h c20 c22 c04 c21
    · exact kr h c22 c21
    have c24 := r1 h c20 c22 c03
    have c32 := r4 h c22 c20 c24
    have c51 := r4 h c13 c14 c32
    exact k1 h c51 c25 c11 c51
  rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
  · exact kr h c13 c11
  · exact kr h c13 c10
  · exact kr h c13 c14
  · have c15 := rc0 h 5 c11 c10 c14 c13 c12
    have c21 := r4 h c10 c15 c05
    have c52 := r3 h c15 c01 c12
    have c25 := r1 h c21 c52 c12
    have c55 := r1 h c52 c25 c21
    have c22 := r1 h c25 c12 c55
    exact kr h c21 c22
  · exact kr h c13 c12
  have c15 := rc4 h 5 c13 c11 c10 c14 c12
  have c21 := r4 h c10 c13 c02
  have c20 := r4 h c01 c04 c15
  have c32 := r3 h c13 c01 c14
  rcases cv4 (op 2 2) with c22|c22|c22|c22|c22|c22
  · exact k1 h c21 c22 c10 c22
  · exact k1 h c21 c22 c11 c21
  · exact kr h c22 c21
  · exact k1 h c21 c22 c13 c20
  · exact kr h c22 c20
  have c23 := r1 h c21 c22 c14
  have c30 := r4 h c02 c01 c23
  rcases cv3 (op 2 4) with c24|c24|c24|c24|c24|c24
  · have c43 := r3 h c24 c02 c22
    exact k1 h c43 c24 c30 c43
  · exact kr h c24 c23
  · exact kr h c24 c21
  · exact kr h c24 c22
  · exact kr h c24 c20
  have c35 := r3 h c23 c12 c24
  exact kr h c32 c35

private theorem n8 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 2) (c02 : op 0 2 = 3) (c03 : op 0 3 = 4) (c04 : op 0 4 = 5) : False := by
  have c05 := rc1 h 5 c00 c01 c02 c03 c04
  rcases cv3 (op 1 0) with c10|c10|c10|c10|c10|c10
  · have c13 := r1 h c10 c01 c02
    exact kr h c10 c13
  · have c51 := r3 h c05 c10 c04
    rcases cv3 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c10 c11 c00 c10
    · exact kr h c11 c10
    · have c13 := r1 h c10 c11 c02
      have c21 := r4 h c11 c10 c13
      rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact kr h c12 c13
      · exact kr h c12 c10
      · exact kr h c12 c11
      · have c32 := r3 h c13 c01 c12
        have c23 := r1 h c21 c32 c12
        have c31 := r4 h c12 c11 c23
        have c33 := r1 h c32 c23 c21
        exact k1 h c33 c23 c31 c33
      · have c24 := r3 h c12 c51 c11
        rcases cv3 (op 1 4) with c14|c14|c14|c14|c14|c14
        · exact kr h c14 c13
        · exact kr h c14 c10
        · exact kr h c14 c11
        · have c32 := r4 h c21 c24 c14
          exact k1 h c13 c01 c32 c14
        · exact kr h c14 c12
        have c15 := rc4 h 5 c13 c10 c11 c14 c12
        have c32 := r4 h c21 c24 c15
        exact k1 h c13 c01 c32 c15
      rcases cv5 (op 1 4) with c14|c14|c14|c14|c14|c14
      · exact kr h c14 c13
      · exact kr h c14 c10
      · exact kr h c14 c11
      · have c15 := rc5 h 5 c13 c10 c11 c14 c12
        have c32 := r3 h c13 c01 c14
        have c23 := r1 h c21 c32 c14
        have c41 := r4 h c12 c11 c23
        have c50 := r4 h c04 c03 c41
        exact k1 h c50 c15 c05 c51
      · exact kr h c14 c12
      have c15 := rc3 h 5 c13 c10 c11 c12 c14
      have c32 := r3 h c13 c01 c15
      have c31 := r4 h c15 c14 c51
      have c23 := r1 h c21 c32 c15
      have c34 := r3 h c23 c12 c21
      exact kr h c31 c34
    · have c15 := r1 h c10 c11 c04
      have c41 := r4 h c11 c10 c15
      rcases cv3 (op 5 2) with c52|c52|c52|c52|c52|c52
      · exact k1 h c15 c01 c52 c10
      · exact k1 h c15 c01 c52 c11
      · have c12 := r1 h c15 c01 c52
        have c20 := r4 h c01 c05 c12
        have c25 := r4 h c52 c52 c20
        have c22 := r4 h c20 c25 c04
        have c42 := r4 h c22 c20 c25
        exact kr h c41 c42
      · exact kr h c52 c51
      · exact k1 h c15 c01 c52 c15
      have c13 := r1 h c15 c01 c52
      rcases cv2 (op 5 0) with c50|c50|c50|c50|c50|c50
      · exact k1 h c50 c05 c01 c52
      · exact k1 h c50 c15 c00 c50
      · exact kr h c50 c52
      · exact kr h c50 c51
      · have c45 := r3 h c04 c50 c03
        have c55 := r1 h c51 c45 c13
        exact k1 h c55 c15 c50 c55
      rcases cv5 (op 5 4) with c54|c54|c54|c54|c54|c54
      · exact k1 h c41 c54 c10 c41
      · have c45 := r4 h c51 c54 c11
        have c14 := r4 h c45 c41 c54
        exact kr h c11 c14
      · exact kr h c54 c50
      · exact kr h c54 c52
      · exact kr h c54 c51
      have c40 := r1 h c41 c54 c15
      have c31 := r3 h c03 c40 c02
      have c55 := r4 h c54 c51 c40
      have c53 := rc1 h 3 c55 c50 c52 c51 c54
      have c30 := r3 h c53 c15 c52
      exact kr h c30 c31
    · exact k1 h c10 c11 c05 c11
    have c14 := r1 h c10 c11 c03
    have c31 := r4 h c11 c10 c14
    rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
    · have c35 := r1 h c30 c03 c04
      exact kr h c30 c35
    · have c21 := r3 h c02 c30 c01
      have c12 := r4 h c21 c21 c10
      exact kr h c12 c14
    · have c40 := r4 h c03 c02 c30
      have c41 := r1 h c40 c04 c05
      exact kr h c40 c41
    · rcases cv1 (op 3 3) with c33|c33|c33|c33|c33|c33
      · exact k1 h c30 c33 c00 c30
      · exact k1 h c30 c33 c02 c33
      · exact kr h c33 c30
      · exact kr h c33 c31
      · exact k1 h c30 c33 c05 c31
      have c43 := r4 h c31 c33 c11
      exact k1 h c43 c14 c30 c43
    · exact kr h c30 c31
    have c25 := r3 h c02 c30 c01
    rcases cv2 (op 1 3) with c13|c13|c13|c13|c13|c13
    · exact kr h c13 c14
    · exact kr h c13 c10
    · exact kr h c13 c11
    · have c42 := r3 h c14 c01 c13
      have c50 := r4 h c04 c03 c42
      have c52 := r1 h c50 c25 c01
      have c21 := r3 h c52 c05 c50
      have c24 := r1 h c21 c02 c13
      exact kr h c24 c25
    · have c20 := r4 h c01 c05 c13
      have c34 := r3 h c13 c51 c11
      have c45 := r3 h c34 c13 c31
      have c53 := r1 h c51 c45 c11
      have c32 := r1 h c30 c53 c01
      exact k1 h c20 c32 c00 c20
    rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
    · exact kr h c12 c14
    · exact kr h c12 c10
    · exact kr h c12 c13
    · exact kr h c12 c11
    · have c15 := rc5 h 5 c14 c10 c13 c11 c12
      have c54 := r3 h c15 c51 c15
      exact k1 h c25 c12 c54 c25
    have c15 := rc4 h 5 c14 c10 c13 c11 c12
    have c20 := r4 h c01 c05 c12
    have c24 := r3 h c12 c51 c13
    have c42 := r3 h c14 c01 c15
    rcases cv5 (op 2 1) with c21|c21|c21|c21|c21|c21
    · have c22 := r4 h c20 c21 c05
      exact k1 h c21 c02 c13 c22
    · exact kr h c21 c25
    · exact kr h c21 c20
    · exact kr h c21 c24
    · exact k1 h c21 c42 c15 c24
    have c52 := r4 h c21 c25 c12
    have c55 := r1 h c52 c25 c21
    have c22 := r1 h c25 c12 c55
    exact kr h c21 c22
  · have c52 := r3 h c05 c10 c04
    rcases cv2 (op 2 1) with c21|c21|c21|c21|c21|c21
    · exact k1 h c10 c21 c00 c10
    · have c12 := r1 h c10 c21 c01
      have c22 := r1 h c21 c12 c10
      have c11 := r1 h c12 c01 c22
      exact kr h c10 c11
    · have c14 := r1 h c10 c21 c03
      rcases cv2 (op 2 0) with c20|c20|c20|c20|c20|c20
      · exact k1 h c01 c20 c10 c02
      · have c30 := r4 h c02 c01 c20
        have c35 := r1 h c30 c03 c04
        exact kr h c30 c35
      · exact kr h c20 c21
      · exact k1 h c01 c20 c14 c00
      · have c25 := r1 h c20 c52 c04
        have c15 := r3 h c01 c20 c05
        have c53 := r3 h c25 c02 c20
        rcases cv5 (op 5 0) with c50|c50|c50|c50|c50|c50
        · exact kr h c50 c53
        · have c51 := r1 h c50 c15 c05
          have c11 := r3 h c51 c05 c50
          exact k1 h c15 c51 c50 c11
        · exact k1 h c50 c25 c00 c50
        · have c31 := r3 h c53 c05 c50
          have c30 := r1 h c31 c03 c14
          exact k1 h c02 c30 c21 c03
        · exact kr h c50 c52
        have c55 := r4 h c50 c53 c02
        have c45 := r4 h c52 c55 c20
        exact k1 h c04 c50 c45 c00
      have c12 := r3 h c01 c20 c05
      rcases cv4 (op 2 2) with c22|c22|c22|c22|c22|c22
      · exact k1 h c20 c22 c00 c20
      · exact k1 h c20 c22 c01 c22
      · exact kr h c22 c20
      · exact kr h c22 c21
      · exact k1 h c20 c22 c05 c21
      have c25 := r1 h c20 c22 c04
      have c51 := r4 h c12 c10 c25
      rcases cv5 (op 2 3) with c23|c23|c23|c23|c23|c23
      · exact kr h c23 c25
      · have c24 := rc5 h 4 c25 c23 c20 c21 c22
        have c53 := r3 h c25 c02 c24
        exact kr h c52 c53
      · exact kr h c23 c20
      · exact kr h c23 c21
      · exact kr h c23 c22
      have c24 := rc1 h 4 c25 c20 c21 c22 c23
      have c45 := r3 h c24 c12 c22
      exact k1 h c45 c24 c51 c45
    · have c15 := r1 h c10 c21 c04
      have c14 := r1 h c15 c01 c52
      have c20 := r4 h c01 c05 c14
      exact kr h c20 c21
    · have c11 := r1 h c10 c21 c05
      rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact kr h c12 c11
      · exact k1 h c11 c01 c12 c11
      · exact kr h c12 c10
      · have c13 := r1 h c11 c01 c12
        have c30 := r3 h c13 c11 c12
        have c22 := r3 h c02 c30 c01
        have c14 := r3 h c21 c52 c22
        exact kr h c10 c14
      · have c14 := r1 h c11 c01 c12
        exact k1 h c21 c52 c14 c21
      have c20 := r4 h c01 c05 c12
      have c15 := r1 h c11 c01 c12
      have c50 := r3 h c15 c11 c12
      rcases cv3 (op 2 2) with c22|c22|c22|c22|c22|c22
      · exact k1 h c20 c22 c00 c20
      · exact k1 h c20 c22 c01 c22
      · exact kr h c22 c20
      · have c25 := r1 h c20 c22 c04
        exact k1 h c50 c25 c00 c50
      · exact kr h c22 c21
      have c24 := r1 h c20 c22 c03
      have c51 := r4 h c12 c10 c24
      exact kr h c51 c52
    have c13 := r1 h c10 c21 c02
    rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
    · exact kr h c12 c13
    · rcases cv4 (op 1 1) with c11|c11|c11|c11|c11|c11
      · exact kr h c11 c13
      · exact kr h c11 c12
      · exact kr h c11 c10
      · have c31 := r4 h c11 c12 c10
        have c32 := r3 h c13 c01 c11
        have c14 := r3 h c31 c03 c32
        exact kr h c10 c14
      · have c20 := r4 h c01 c05 c11
        have c22 := r4 h c21 c20 c13
        have c32 := r4 h c22 c21 c20
        exact k1 h c13 c01 c32 c10
      have c41 := r4 h c11 c12 c10
      have c24 := r3 h c12 c11 c10
      rcases cv5 (op 1 4) with c14|c14|c14|c14|c14|c14
      · exact kr h c14 c13
      · exact kr h c14 c12
      · exact kr h c14 c10
      · have c15 := rc5 h 5 c13 c12 c10 c14 c11
        have c45 := r1 h c41 c04 c15
        exact k1 h c52 c45 c21 c52
      · exact kr h c14 c11
      have c15 := rc3 h 5 c13 c12 c10 c11 c14
      have c43 := r1 h c41 c04 c15
      exact k1 h c24 c02 c43 c21
    · exact kr h c12 c10
    · have c32 := r3 h c13 c01 c12
      have c23 := r4 h c32 c32 c21
      have c22 := r4 h c21 c23 c12
      exact kr h c21 c22
    · have c20 := r4 h c01 c05 c12
      exact kr h c20 c21
    rcases cv4 (op 2 2) with c22|c22|c22|c22|c22|c22
    · exact k1 h c21 c22 c10 c22
    · have c11 := r3 h c21 c22 c22
      exact kr h c10 c11
    · exact kr h c22 c21
    · have c20 := r1 h c21 c22 c13
      have c32 := r4 h c22 c21 c20
      exact k1 h c13 c01 c32 c10
    · have c24 := r3 h c22 c52 c21
      have c15 := r3 h c21 c22 c24
      exact kr h c12 c15
    rcases cv3 (op 1 4) with c14|c14|c14|c14|c14|c14
    · exact kr h c14 c13
    · exact k1 h c21 c22 c14 c21
    · exact kr h c14 c10
    · exact kr h c14 c12
    · have c20 := r4 h c01 c05 c14
      exact kr h c20 c22
    have c23 := r1 h c21 c22 c14
    have c42 := r4 h c22 c21 c23
    have c50 := r4 h c04 c03 c42
    rcases cv5 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact kr h c11 c13
    · have c15 := rc5 h 5 c13 c11 c10 c14 c12
      have c20 := r4 h c01 c05 c15
      have c25 := r1 h c20 c52 c04
      exact k1 h c50 c25 c00 c50
    · exact kr h c11 c10
    · exact kr h c11 c14
    · exact kr h c11 c12
    have c15 := rc1 h 5 c13 c10 c14 c12 c11
    have c51 := r4 h c11 c15 c11
    have c55 := r1 h c51 c15 c11
    exact k1 h c55 c15 c51 c51
  · have c54 := r3 h c05 c10 c04
    rcases cv2 (op 4 0) with c40|c40|c40|c40|c40|c40
    · have c41 := r1 h c40 c04 c05
      exact kr h c40 c41
    · have c31 := r3 h c03 c40 c02
      rcases cv2 (op 4 1) with c41|c41|c41|c41|c41|c41
      · exact k1 h c10 c41 c00 c10
      · exact kr h c41 c40
      · have c14 := r1 h c10 c41 c03
        exact k1 h c40 c14 c00 c40
      · have c15 := r1 h c10 c41 c04
        have c44 := r4 h c41 c40 c15
        have c45 := r1 h c44 c54 c44
        have c55 := r1 h c54 c45 c44
        exact k1 h c55 c45 c54 c54
      · have c11 := r1 h c10 c41 c05
        have c14 := r3 h c41 c54 c40
        exact kr h c11 c14
      have c13 := r1 h c10 c41 c02
      have c24 := r4 h c41 c40 c13
      rcases cv1 (op 1 4) with c14|c14|c14|c14|c14|c14
      · exact kr h c14 c13
      · have c43 := r1 h c40 c14 c02
        have c21 := r4 h c14 c10 c43
        exact kr h c21 c24
      · have c44 := r1 h c40 c14 c03
        have c42 := r3 h c14 c31 c10
        exact kr h c42 c44
      · exact kr h c14 c10
      · exact k1 h c40 c14 c05 c41
      have c42 := r1 h c40 c14 c01
      have c25 := r3 h c42 c04 c41
      have c11 := r4 h c14 c10 c42
      have c21 := r4 h c11 c14 c10
      have c20 := r1 h c21 c02 c13
      exact kr h c20 c25
    · have c50 := r4 h c04 c03 c40
      have c52 := r1 h c50 c05 c01
      exact kr h c50 c52
    · have c45 := r4 h c54 c54 c40
      have c44 := r4 h c40 c45 c04
      exact kr h c40 c44
    · have c45 := r1 h c40 c54 c04
      have c55 := r1 h c54 c45 c40
      have c44 := r1 h c45 c04 c55
      exact kr h c40 c44
    have c32 := r3 h c03 c40 c02
    rcases cv0 (op 4 4) with c44|c44|c44|c44|c44|c44
    · rcases cv4 (op 4 1) with c41|c41|c41|c41|c41|c41
      · exact k1 h c10 c41 c00 c10
      · exact kr h c41 c44
      · exact kr h c41 c40
      · have c14 := r1 h c10 c41 c03
        have c42 := r3 h c14 c01 c10
        exact k1 h c44 c14 c40 c42
      · have c14 := r3 h c41 c54 c44
        exact k1 h c44 c14 c44 c41
      have c14 := r4 h c44 c41 c44
      have c45 := r4 h c54 c54 c41
      exact k1 h c45 c14 c54 c44
    · exact kr h c44 c40
    · have c50 := r4 h c04 c03 c44
      exact kr h c50 c54
    · have c45 := r4 h c54 c54 c44
      exact k1 h c45 c44 c54 c44
    · have c45 := r1 h c44 c54 c44
      have c55 := r1 h c54 c45 c44
      exact k1 h c55 c45 c54 c54
    have c24 := r4 h c40 c44 c03
    rcases cv1 (op 4 2) with c42|c42|c42|c42|c42|c42
    · exact kr h c42 c44
    · exact kr h c42 c40
    · have c23 := r1 h c24 c32 c42
      have c33 := r1 h c32 c23 c24
      have c22 := r1 h c23 c42 c33
      exact kr h c22 c24
    · exact k1 h c24 c32 c42 c24
    · have c43 := r1 h c42 c54 c24
      exact kr h c40 c43
    have c21 := r1 h c24 c32 c42
    rcases cv5 (op 4 1) with c41|c41|c41|c41|c41|c41
    · exact kr h c41 c44
    · exact kr h c41 c42
    · exact kr h c41 c40
    · have c14 := r1 h c10 c41 c03
      have c11 := r1 h c14 c01 c42
      exact kr h c10 c11
    · exact k1 h c41 c44 c10 c44
    have c11 := r1 h c10 c41 c05
    have c20 := r1 h c21 c42 c11
    exact k1 h c01 c20 c11 c00
  · have c20 := r4 h c01 c05 c10
    have c24 := r1 h c20 c02 c03
    exact kr h c20 c24
  have c53 := r3 h c05 c10 c04
  rcases cv4 (op 3 0) with c30|c30|c30|c30|c30|c30
  · have c35 := r1 h c30 c03 c04
    exact kr h c30 c35
  · have c21 := r3 h c02 c30 c01
    rcases cv4 (op 1 1) with c11|c11|c11|c11|c11|c11
    · have c31 := r4 h c10 c11 c05
      have c14 := r3 h c31 c53 c30
      exact kr h c11 c14
    · have c12 := r4 h c21 c21 c11
      exact k1 h c12 c11 c21 c11
    · have c12 := r1 h c11 c21 c11
      have c22 := r1 h c21 c12 c11
      exact k1 h c22 c12 c21 c21
    · exact kr h c11 c10
    · have c20 := r4 h c01 c05 c11
      exact kr h c20 c21
    rcases cv2 (op 1 3) with c13|c13|c13|c13|c13|c13
    · exact k1 h c30 c13 c00 c30
    · have c12 := r4 h c21 c21 c13
      exact kr h c10 c12
    · exact kr h c13 c10
    · exact kr h c13 c11
    · have c31 := r1 h c30 c13 c05
      exact k1 h c10 c31 c00 c10
    have c33 := r1 h c30 c13 c02
    have c31 := r3 h c13 c21 c10
    exact kr h c31 c33
  · have c40 := r4 h c03 c02 c30
    have c41 := r1 h c40 c04 c05
    exact kr h c40 c41
  · have c23 := r3 h c02 c30 c01
    rcases cv4 (op 3 1) with c31|c31|c31|c31|c31|c31
    · exact k1 h c10 c31 c00 c10
    · have c12 := r1 h c10 c31 c01
      exact k1 h c23 c12 c30 c23
    · have c13 := r1 h c10 c31 c02
      have c32 := r3 h c13 c01 c10
      have c33 := r4 h c30 c32 c01
      exact k1 h c33 c13 c30 c33
    · exact kr h c31 c30
    · rcases cv4 (op 3 3) with c33|c33|c33|c33|c33|c33
      · exact k1 h c30 c33 c00 c30
      · have c14 := r3 h c31 c53 c33
        exact kr h c10 c14
      · exact k1 h c30 c33 c02 c33
      · exact kr h c33 c30
      · exact kr h c33 c31
      have c35 := r1 h c30 c33 c04
      have c43 := r4 h c33 c30 c35
      have c54 := r3 h c35 c03 c31
      have c45 := r1 h c43 c54 c31
      exact k1 h c53 c45 c33 c54
    rcases cv1 (op 3 3) with c33|c33|c33|c33|c33|c33
    · exact k1 h c30 c33 c00 c30
    · exact k1 h c30 c33 c02 c33
    · exact kr h c33 c30
    · exact kr h c33 c31
    · exact k1 h c30 c33 c05 c31
    have c32 := r1 h c30 c33 c01
    have c43 := r4 h c31 c33 c10
    rcases cv2 (op 3 4) with c34|c34|c34|c34|c34|c34
    · exact kr h c34 c32
    · exact kr h c34 c33
    · exact kr h c34 c30
    · exact kr h c34 c31
    · have c35 := rc2 h 5 c32 c33 c30 c31 c34
      have c51 := r3 h c35 c23 c34
      exact kr h c51 c53
    have c24 := r3 h c32 c03 c34
    have c40 := r4 h c03 c02 c34
    have c42 := r4 h c24 c24 c40
    exact kr h c42 c43
  · have c35 := r1 h c30 c53 c04
    have c54 := r3 h c35 c03 c30
    have c41 := r3 h c54 c05 c53
    have c50 := r4 h c04 c03 c41
    have c15 := r4 h c50 c54 c03
    exact kr h c10 c15
  have c24 := r3 h c02 c30 c01
  rcases cv3 (op 3 2) with c32|c32|c32|c32|c32|c32
  · have c43 := r4 h c30 c32 c01
    have c31 := r1 h c32 c03 c24
    have c40 := r4 h c03 c02 c31
    exact kr h c40 c43
  · rcases cv3 (op 3 1) with c31|c31|c31|c31|c31|c31
    · exact k1 h c10 c31 c00 c10
    · exact kr h c31 c32
    · have c13 := r1 h c10 c31 c02
      have c11 := r1 h c13 c01 c32
      exact kr h c10 c11
    · exact kr h c31 c30
    · have c11 := r1 h c10 c31 c05
      have c14 := r3 h c31 c53 c32
      rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
      · exact kr h c12 c11
      · exact k1 h c11 c01 c12 c11
      · exact kr h c12 c14
      · exact kr h c12 c10
      · exact k1 h c11 c01 c12 c14
      have c15 := r1 h c11 c01 c12
      have c13 := rc4 h 3 c11 c15 c14 c10 c12
      exact k1 h c32 c13 c24 c31
    rcases cv2 (op 3 3) with c33|c33|c33|c33|c33|c33
    · exact k1 h c31 c33 c10 c33
    · exact kr h c33 c32
    · exact kr h c33 c31
    · exact kr h c33 c30
    · have c34 := r3 h c33 c53 c31
      exact kr h c32 c34
    have c12 := r3 h c31 c33 c32
    have c40 := r4 h c03 c02 c33
    have c23 := r4 h c33 c31 c32
    have c50 := r4 h c04 c03 c40
    have c52 := r1 h c50 c05 c01
    have c21 := r4 h c12 c12 c23
    exact k1 h c52 c05 c21 c53
  · have c40 := r4 h c03 c02 c32
    have c42 := r1 h c40 c24 c01
    have c25 := r3 h c42 c04 c40
    exact k1 h c25 c02 c53 c24
  · exact kr h c32 c30
  · have c31 := r1 h c32 c53 c24
    have c13 := r1 h c10 c31 c02
    have c15 := r1 h c13 c01 c32
    exact kr h c10 c15
  rcases cv1 (op 3 1) with c31|c31|c31|c31|c31|c31
  · exact k1 h c10 c31 c00 c10
  · have c13 := r1 h c10 c31 c02
    exact k1 h c13 c01 c32 c13
  · exact kr h c31 c32
  · exact kr h c31 c30
  · rcases cv0 (op 3 3) with c33|c33|c33|c33|c33|c33
    · have c14 := r3 h c31 c53 c33
      exact kr h c10 c14
    · have c22 := r3 h c32 c33 c33
      have c23 := r4 h c33 c32 c33
      exact kr h c22 c23
    · exact kr h c33 c32
    · exact kr h c33 c30
    · exact kr h c33 c31
    have c43 := r4 h c30 c33 c02
    have c45 := r1 h c43 c24 c31
    have c50 := r1 h c53 c45 c33
    exact k1 h c04 c50 c43 c02
  have c12 := r1 h c10 c31 c01
  rcases cv0 (op 3 3) with c33|c33|c33|c33|c33|c33
  · exact kr h c33 c31
  · have c40 := r4 h c03 c02 c33
    have c23 := r4 h c33 c32 c33
    exact k1 h c24 c12 c40 c23
  · exact kr h c33 c32
  · exact kr h c33 c30
  · have c34 := r3 h c33 c53 c32
    have c40 := r4 h c03 c02 c34
    exact k1 h c24 c12 c40 c24
  have c43 := r4 h c30 c33 c02
  have c34 := r3 h c33 c03 c32
  have c41 := r1 h c43 c24 c31
  have c40 := r1 h c41 c34 c12
  exact k1 h c03 c40 c31 c01

private theorem sym5 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 2) (c02 : op 0 2 = 3) (c03 : op 0 3 = 4) : False := by
  rcases cv5 (op 0 4) with c04|c04|c04|c04|c04|c04
  · exact kr h c04 c00
  · exact n7 h c00 c01 c02 c03 c04
  · exact kr h c04 c01
  · exact kr h c04 c02
  · exact kr h c04 c03
  exact n8 h c00 c01 c02 c03 c04

private theorem sym6 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 2) (c02 : op 0 2 = 3) : False := by
  rcases cv1 (op 0 3) with c03|c03|c03|c03|c03|c03
  · exact kr h c03 c00
  · exact kr h c03 c01
  · exact kr h c03 c02
  · exact sym5 h c00 c01 c02 c03
  · exact sym5 (h.cj (sw 4 5)) (cc c00) (cc c01) (cc c02) (cc c03)
  rcases cv4 (op 0 4) with c04|c04|c04|c04|c04|c04
  · exact kr h c04 c00
  · exact kr h c04 c03
  · exact kr h c04 c01
  · exact kr h c04 c02
  · exact n6 h c00 c01 c02 c03 c04
  have c05 := rc5 h 5 c00 c03 c01 c02 c04
  rcases cv2 (op 1 0) with c10|c10|c10|c10|c10|c10
  · have c13 := r1 h c10 c01 c02
    exact kr h c10 c13
  · have c31 := r3 h c03 c10 c02
    rcases cv2 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact k1 h c10 c11 c00 c10
    · exact kr h c11 c10
    · exact k1 h c10 c11 c03 c11
    · have c14 := r1 h c10 c11 c04
      have c41 := r4 h c11 c10 c14
      have c40 := r4 h c04 c04 c41
      have c42 := r3 h c14 c01 c11
      exact kr h c40 c42
    · have c15 := r1 h c10 c11 c05
      have c51 := r4 h c11 c10 c15
      have c50 := r4 h c05 c05 c51
      have c52 := r3 h c15 c01 c11
      exact kr h c50 c52
    have c13 := r1 h c10 c11 c02
    have c21 := r4 h c11 c10 c13
    rcases cv5 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c20 c02 c03 c21
    · exact k1 h c01 c20 c11 c02
    · have c12 := r3 h c01 c20 c03
      have c32 := r3 h c13 c01 c12
      exact kr h c31 c32
    · exact kr h c20 c21
    · have c14 := r3 h c01 c20 c03
      have c32 := r3 h c13 c01 c14
      have c23 := r1 h c21 c32 c14
      exact k1 h c31 c23 c11 c32
    have c15 := r3 h c01 c20 c03
    have c32 := r3 h c13 c01 c15
    have c23 := r1 h c21 c32 c15
    exact k1 h c31 c23 c11 c32
  · have c20 := r4 h c01 c03 c10
    have c21 := r1 h c20 c02 c03
    exact kr h c20 c21
  · have c34 := r3 h c03 c10 c02
    rcases cv5 (op 4 0) with c40|c40|c40|c40|c40|c40
    · exact k1 h c04 c40 c40 c00
    · have c41 := r3 h c04 c40 c04
      have c14 := r1 h c10 c41 c04
      exact k1 h c40 c14 c00 c40
    · have c42 := r3 h c04 c40 c04
      rcases cv5 (op 4 4) with c44|c44|c44|c44|c44|c44
      · have c24 := r4 h c40 c44 c04
        have c20 := r3 h c42 c44 c40
        exact k1 h c24 c42 c44 c20
      · have c14 := r4 h c44 c42 c40
        exact k1 h c14 c01 c42 c14
      · exact kr h c44 c40
      · exact k1 h c44 c34 c42 c44
      · exact kr h c44 c42
      have c25 := r3 h c42 c44 c40
      have c54 := r4 h c44 c42 c40
      rcases cv5 (op 2 4) with c24|c24|c24|c24|c24|c24
      · exact kr h c24 c25
      · exact k1 h c40 c24 c01 c42
      · have c43 := r1 h c40 c24 c02
        exact k1 h c43 c04 c34 c42
      · have c41 := r1 h c40 c24 c03
        exact k1 h c10 c41 c00 c10
      · exact k1 h c40 c24 c04 c44
      have c45 := r1 h c40 c24 c05
      have c50 := r1 h c54 c05 c45
      exact k1 h c05 c50 c54 c00
    · have c43 := r1 h c40 c34 c02
      exact k1 h c04 c40 c43 c00
    · have c44 := r3 h c04 c40 c04
      exact kr h c40 c44
    have c45 := r3 h c04 c40 c04
    rcases cv2 (op 4 4) with c44|c44|c44|c44|c44|c44
    · exact k1 h c44 c04 c44 c40
    · have c14 := r4 h c44 c45 c40
      have c41 := r4 h c10 c14 c04
      have c11 := r3 h c41 c44 c44
      exact kr h c10 c11
    · have c42 := r3 h c44 c34 c45
      exact kr h c40 c42
    · exact kr h c44 c45
    · exact kr h c44 c40
    have c24 := r4 h c44 c45 c40
    have c52 := r3 h c45 c44 c40
    rcases cv3 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact kr h c20 c24
    · have c12 := r4 h c20 c24 c04
      exact kr h c10 c12
    · have c22 := r4 h c20 c24 c04
      have c43 := r3 h c24 c02 c22
      exact kr h c43 c44
    · have c42 := r4 h c20 c24 c04
      have c22 := r3 h c42 c44 c44
      exact kr h c20 c22
    · exact k1 h c20 c52 c00 c20
    have c32 := r4 h c20 c24 c04
    have c23 := r4 h c34 c32 c44
    have c43 := r4 h c32 c34 c23
    exact k1 h c43 c34 c32 c44
  · have c35 := r3 h c03 c10 c02
    rcases cv4 (op 5 0) with c50|c50|c50|c50|c50|c50
    · exact k1 h c05 c50 c50 c00
    · have c51 := r3 h c05 c50 c05
      have c15 := r1 h c10 c51 c05
      exact k1 h c50 c15 c00 c50
    · have c52 := r3 h c05 c50 c05
      rcases cv4 (op 5 5) with c55|c55|c55|c55|c55|c55
      · have c25 := r4 h c50 c55 c05
        have c20 := r3 h c52 c55 c50
        exact k1 h c25 c52 c55 c20
      · have c15 := r4 h c55 c52 c50
        exact k1 h c15 c01 c52 c15
      · exact kr h c55 c50
      · exact k1 h c55 c35 c52 c55
      · exact kr h c55 c52
      have c24 := r3 h c52 c55 c50
      have c45 := r4 h c55 c52 c50
      rcases cv4 (op 2 5) with c25|c25|c25|c25|c25|c25
      · exact kr h c25 c24
      · exact k1 h c50 c25 c01 c52
      · have c53 := r1 h c50 c25 c02
        exact k1 h c53 c05 c35 c52
      · have c51 := r1 h c50 c25 c03
        exact k1 h c10 c51 c00 c10
      · exact k1 h c50 c25 c05 c55
      have c54 := r1 h c50 c25 c04
      exact k1 h c54 c05 c45 c50
    · have c53 := r1 h c50 c35 c02
      exact k1 h c05 c50 c53 c00
    · have c55 := r3 h c05 c50 c05
      exact kr h c50 c55
    have c54 := r3 h c05 c50 c05
    rcases cv2 (op 5 5) with c55|c55|c55|c55|c55|c55
    · have c45 := r4 h c50 c55 c05
      have c40 := r3 h c54 c55 c50
      exact k1 h c45 c54 c55 c40
    · have c15 := r4 h c55 c54 c50
      have c51 := r4 h c10 c15 c05
      have c11 := r3 h c51 c55 c55
      exact kr h c10 c11
    · have c52 := r3 h c55 c35 c54
      exact kr h c50 c52
    · exact kr h c55 c50
    · exact kr h c55 c54
    have c42 := r3 h c54 c55 c50
    have c25 := r4 h c55 c54 c50
    rcases cv3 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact kr h c20 c25
    · have c12 := r4 h c20 c25 c05
      exact kr h c10 c12
    · have c22 := r4 h c20 c25 c05
      have c52 := r4 h c22 c20 c25
      exact kr h c52 c54
    · exact k1 h c20 c42 c00 c20
    · have c52 := r4 h c20 c25 c05
      have c22 := r3 h c52 c55 c55
      exact kr h c20 c22
    have c32 := r4 h c20 c25 c05
    have c23 := r4 h c35 c32 c55
    have c53 := r4 h c32 c35 c23
    exact k1 h c53 c35 c32 c55
  have c32 := r3 h c03 c10 c02
  rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
  · exact k1 h c30 c03 c01 c32
  · have c21 := r3 h c02 c30 c01
    have c12 := r1 h c10 c21 c01
    have c22 := r1 h c21 c12 c10
    have c11 := r1 h c12 c01 c22
    exact kr h c10 c11
  · exact kr h c30 c32
  · have c23 := r3 h c02 c30 c01
    have c21 := r3 h c32 c23 c32
    have c13 := r1 h c10 c21 c02
    have c12 := r1 h c13 c01 c32
    have c20 := r4 h c01 c03 c12
    exact kr h c20 c21
  · have c24 := r3 h c02 c30 c01
    rcases cv5 (op 2 3) with c23|c23|c23|c23|c23|c23
    · have c20 := r3 h c32 c23 c32
      have c22 := r4 h c20 c23 c02
      exact kr h c20 c22
    · exact kr h c23 c24
    · have c22 := r3 h c32 c23 c32
      exact k1 h c23 c22 c32 c22
    · have c33 := r1 h c32 c23 c23
      exact k1 h c33 c23 c33 c32
    · have c31 := r1 h c32 c23 c24
      exact kr h c31 c32
    have c25 := r3 h c32 c23 c32
    rcases cv4 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c01 c20 c10 c02
    · exact kr h c20 c24
    · exact kr h c20 c25
    · exact k1 h c20 c32 c02 c23
    · exact kr h c20 c23
    have c14 := r3 h c01 c20 c03
    rcases cv3 (op 2 1) with c21|c21|c21|c21|c21|c21
    · exact k1 h c10 c21 c00 c10
    · exact kr h c21 c24
    · exact kr h c21 c25
    · exact kr h c21 c20
    · exact kr h c21 c23
    have c22 := rc0 h 2 c24 c25 c21 c20 c23
    have c42 := r4 h c20 c22 c01
    have c12 := r3 h c21 c32 c24
    have c41 := r4 h c12 c10 c22
    have c45 := r1 h c42 c14 c23
    exact kr h c41 c45
  have c25 := r3 h c02 c30 c01
  rcases cv4 (op 2 3) with c23|c23|c23|c23|c23|c23
  · have c20 := r3 h c32 c23 c32
    have c22 := r4 h c20 c23 c02
    exact kr h c20 c22
  · exact kr h c23 c25
  · have c22 := r3 h c32 c23 c32
    exact k1 h c23 c22 c32 c22
  · have c33 := r1 h c32 c23 c23
    exact k1 h c33 c23 c33 c32
  · have c31 := r1 h c32 c23 c25
    exact kr h c31 c32
  have c24 := r3 h c32 c23 c32
  rcases cv5 (op 2 0) with c20|c20|c20|c20|c20|c20
  · exact k1 h c01 c20 c10 c02
  · exact kr h c20 c25
  · exact kr h c20 c24
  · exact k1 h c20 c32 c02 c23
  · exact kr h c20 c23
  have c15 := r3 h c01 c20 c03
  rcases cv3 (op 2 1) with c21|c21|c21|c21|c21|c21
  · exact k1 h c10 c21 c00 c10
  · exact kr h c21 c25
  · exact kr h c21 c24
  · exact kr h c21 c23
  · exact kr h c21 c20
  have c22 := rc0 h 2 c25 c24 c21 c23 c20
  have c52 := r4 h c20 c22 c01
  have c12 := r3 h c21 c32 c25
  have c51 := r4 h c12 c10 c22
  have c54 := r1 h c52 c15 c23
  exact kr h c51 c54

private theorem sym7 {op : Op} (h : H op) (c00 : op 0 0 = 0) (c01 : op 0 1 = 2) : False := by
  rcases cv1 (op 0 2) with c02|c02|c02|c02|c02|c02
  · exact kr h c02 c00
  · exact kr h c02 c01
  · exact sym6 h c00 c01 c02
  · exact sym6 (h.cj (sw 3 4)) (cc c00) (cc c01) (cc c02)
  · exact sym6 (h.cj (sw 3 5)) (cc c00) (cc c01) (cc c02)
  rcases cv3 (op 0 3) with c03|c03|c03|c03|c03|c03
  · exact kr h c03 c00
  · exact kr h c03 c02
  · exact kr h c03 c01
  · exact sym4 h c00 c01 c02 c03
  · exact sym4 (h.cj (sw 4 5)) (cc c00) (cc c01) (cc c02) (cc c03)
  rcases cv4 (op 0 4) with c04|c04|c04|c04|c04|c04
  · exact kr h c04 c00
  · exact kr h c04 c02
  · exact kr h c04 c01
  · exact kr h c04 c03
  · exact n3 h c00 c01 c02 c03 c04
  have c05 := rc5 h 5 c00 c02 c01 c03 c04
  rcases cv5 (op 1 0) with c10|c10|c10|c10|c10|c10
  · have c11 := r1 h c10 c01 c02
    exact kr h c10 c11
  · have c21 := r3 h c02 c10 c01
    have c12 := r4 h c21 c21 c10
    have c11 := r4 h c10 c12 c01
    exact kr h c10 c11
  · have c20 := r4 h c01 c02 c10
    have c22 := r3 h c02 c10 c01
    exact k1 h c20 c02 c01 c22
  · have c23 := r3 h c02 c10 c01
    rcases cv5 (op 2 1) with c21|c21|c21|c21|c21|c21
    · have c11 := r3 h c21 c02 c23
      exact kr h c10 c11
    · exact kr h c21 c23
    · have c22 := r4 h c21 c23 c10
      exact k1 h c22 c02 c21 c22
    · have c32 := r4 h c21 c23 c10
      have c31 := r1 h c32 c03 c23
      have c11 := r1 h c10 c31 c02
      have c30 := r1 h c31 c23 c11
      exact k1 h c03 c30 c31 c02
    · have c42 := r4 h c21 c23 c10
      rcases cv5 (op 2 0) with c20|c20|c20|c20|c20|c20
      · exact k1 h c01 c20 c10 c03
      · exact kr h c20 c23
      · have c12 := r3 h c01 c20 c02
        have c24 := r3 h c12 c21 c12
        exact k1 h c42 c04 c24 c42
      · have c13 := r3 h c01 c20 c02
        have c34 := r3 h c13 c21 c10
        have c12 := r4 h c23 c20 c34
        have c41 := r4 h c12 c13 c20
        exact kr h c41 c42
      · exact kr h c20 c21
      have c15 := r3 h c01 c20 c02
      rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c22 := r3 h c12 c01 c15
        exact kr h c20 c22
      · have c11 := r4 h c12 c15 c20
        exact k1 h c11 c01 c12 c11
      · exact kr h c12 c15
      · exact kr h c12 c10
      · have c41 := r4 h c12 c15 c20
        exact kr h c41 c42
      have c51 := r4 h c12 c15 c20
      have c54 := r3 h c15 c21 c12
      have c52 := r1 h c51 c05 c15
      have c22 := r3 h c52 c15 c54
      exact kr h c21 c22
    have c52 := r4 h c21 c23 c10
    rcases cv4 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c01 c20 c10 c03
    · exact kr h c20 c23
    · have c12 := r3 h c01 c20 c02
      have c25 := r3 h c12 c21 c12
      exact k1 h c52 c05 c25 c52
    · have c13 := r3 h c01 c20 c02
      have c35 := r3 h c13 c21 c10
      have c12 := r4 h c23 c20 c35
      have c51 := r4 h c12 c13 c20
      exact kr h c51 c52
    · exact kr h c20 c21
    have c14 := r3 h c01 c20 c02
    rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c22 := r3 h c12 c01 c14
      exact kr h c20 c22
    · have c11 := r4 h c12 c14 c20
      exact k1 h c11 c01 c12 c11
    · exact kr h c12 c14
    · exact kr h c12 c10
    · have c51 := r4 h c12 c14 c20
      exact kr h c51 c52
    have c41 := r4 h c12 c14 c20
    have c45 := r3 h c14 c21 c12
    have c42 := r1 h c41 c04 c14
    have c22 := r3 h c42 c14 c45
    exact kr h c21 c22
  · have c24 := r3 h c02 c10 c01
    rcases cv5 (op 2 1) with c21|c21|c21|c21|c21|c21
    · have c11 := r3 h c21 c02 c24
      exact kr h c10 c11
    · exact kr h c21 c24
    · have c22 := r4 h c21 c24 c10
      exact k1 h c22 c02 c21 c22
    · have c32 := r4 h c21 c24 c10
      rcases cv5 (op 2 0) with c20|c20|c20|c20|c20|c20
      · exact k1 h c01 c20 c10 c04
      · exact kr h c20 c24
      · have c12 := r3 h c01 c20 c02
        have c23 := r3 h c12 c21 c12
        exact k1 h c32 c03 c23 c32
      · exact kr h c20 c21
      · have c14 := r3 h c01 c20 c02
        have c43 := r3 h c14 c21 c10
        have c12 := r4 h c24 c20 c43
        have c31 := r4 h c12 c14 c20
        exact kr h c31 c32
      have c15 := r3 h c01 c20 c02
      rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c22 := r3 h c12 c01 c15
        exact kr h c20 c22
      · have c11 := r4 h c12 c15 c20
        exact k1 h c11 c01 c12 c11
      · exact kr h c12 c15
      · have c31 := r4 h c12 c15 c20
        exact kr h c31 c32
      · exact kr h c12 c10
      have c51 := r4 h c12 c15 c20
      have c53 := r3 h c15 c21 c12
      have c52 := r1 h c51 c05 c15
      have c22 := r3 h c52 c15 c53
      exact kr h c21 c22
    · have c42 := r4 h c21 c24 c10
      have c41 := r1 h c42 c04 c24
      have c11 := r1 h c10 c41 c02
      have c40 := r1 h c41 c24 c11
      exact k1 h c04 c40 c41 c02
    have c52 := r4 h c21 c24 c10
    rcases cv3 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c01 c20 c10 c04
    · exact kr h c20 c24
    · have c12 := r3 h c01 c20 c02
      have c25 := r3 h c12 c21 c12
      exact k1 h c52 c05 c25 c52
    · have c14 := r3 h c01 c20 c02
      have c45 := r3 h c14 c21 c10
      have c12 := r4 h c24 c20 c45
      have c51 := r4 h c12 c14 c20
      exact kr h c51 c52
    · exact kr h c20 c21
    have c13 := r3 h c01 c20 c02
    rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c22 := r3 h c12 c01 c13
      exact kr h c20 c22
    · have c11 := r4 h c12 c13 c20
      exact k1 h c11 c01 c12 c11
    · exact kr h c12 c13
    · exact kr h c12 c10
    · have c51 := r4 h c12 c13 c20
      exact kr h c51 c52
    have c31 := r4 h c12 c13 c20
    have c35 := r3 h c13 c21 c12
    have c32 := r1 h c31 c03 c13
    have c22 := r3 h c32 c13 c35
    exact kr h c21 c22
  have c25 := r3 h c02 c10 c01
  rcases cv4 (op 2 1) with c21|c21|c21|c21|c21|c21
  · have c11 := r3 h c21 c02 c25
    exact kr h c10 c11
  · exact kr h c21 c25
  · have c22 := r4 h c21 c25 c10
    exact k1 h c22 c02 c21 c22
  · have c32 := r4 h c21 c25 c10
    rcases cv4 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c01 c20 c10 c05
    · exact kr h c20 c25
    · have c12 := r3 h c01 c20 c02
      have c23 := r3 h c12 c21 c12
      exact k1 h c32 c03 c23 c32
    · exact kr h c20 c21
    · have c15 := r3 h c01 c20 c02
      have c53 := r3 h c15 c21 c10
      have c12 := r4 h c25 c20 c53
      have c31 := r4 h c12 c15 c20
      exact kr h c31 c32
    have c14 := r3 h c01 c20 c02
    rcases cv4 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c22 := r3 h c12 c01 c14
      exact kr h c20 c22
    · have c11 := r4 h c12 c14 c20
      exact k1 h c11 c01 c12 c11
    · exact kr h c12 c14
    · have c31 := r4 h c12 c14 c20
      exact kr h c31 c32
    · exact kr h c12 c10
    have c41 := r4 h c12 c14 c20
    have c43 := r3 h c14 c21 c12
    have c42 := r1 h c41 c04 c14
    have c22 := r3 h c42 c14 c43
    exact kr h c21 c22
  · have c52 := r4 h c21 c25 c10
    have c51 := r1 h c52 c05 c25
    have c11 := r1 h c10 c51 c02
    have c50 := r1 h c51 c25 c11
    exact k1 h c05 c50 c51 c02
  have c42 := r4 h c21 c25 c10
  rcases cv3 (op 2 0) with c20|c20|c20|c20|c20|c20
  · exact k1 h c01 c20 c10 c05
  · exact kr h c20 c25
  · have c12 := r3 h c01 c20 c02
    have c24 := r3 h c12 c21 c12
    exact k1 h c42 c04 c24 c42
  · exact kr h c20 c21
  · have c15 := r3 h c01 c20 c02
    have c54 := r3 h c15 c21 c10
    have c12 := r4 h c25 c20 c54
    have c41 := r4 h c12 c15 c20
    exact kr h c41 c42
  have c13 := r3 h c01 c20 c02
  rcases cv3 (op 1 2) with c12|c12|c12|c12|c12|c12
  · have c22 := r3 h c12 c01 c13
    exact kr h c20 c22
  · have c11 := r4 h c12 c13 c20
    exact k1 h c11 c01 c12 c11
  · exact kr h c12 c13
  · have c41 := r4 h c12 c13 c20
    exact kr h c41 c42
  · exact kr h c12 c10
  have c31 := r4 h c12 c13 c20
  have c34 := r3 h c13 c21 c12
  have c32 := r1 h c31 c03 c13
  have c22 := r3 h c32 c13 c34
  exact kr h c21 c22

private theorem n9 {op : Op} (h : H op) (c00 : op 0 0 = 1) (c01 : op 0 1 = 2) (c02 : op 0 2 = 3) (c03 : op 0 3 = 4) (c04 : op 0 4 = 5) : False := by
  have c05 := rc0 h 5 c00 c01 c02 c03 c04
  have c10 := r4 h c00 c05 c04
  have c51 := r3 h c05 c00 c04
  rcases cv1 (op 1 1) with c11|c11|c11|c11|c11|c11
  · have c20 := r4 h c01 c00 c11
    have c30 := r4 h c02 c01 c20
    have c35 := r1 h c30 c03 c04
    exact kr h c30 c35
  · rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c20 := r4 h c01 c00 c12
      have c22 := r3 h c12 c01 c11
      exact k1 h c22 c12 c20 c22
    · have c21 := r4 h c11 c12 c11
      have c22 := r1 h c21 c12 c11
      exact k1 h c22 c12 c21 c21
    · exact kr h c12 c11
    · rcases cv5 (op 3 0) with c30|c30|c30|c30|c30|c30
      · have c20 := r3 h c02 c30 c01
        have c31 := r4 h c12 c11 c20
        exact kr h c30 c31
      · have c21 := r3 h c02 c30 c01
        have c31 := r4 h c12 c11 c21
        exact kr h c30 c31
      · have c22 := r3 h c02 c30 c01
        have c31 := r4 h c12 c11 c22
        exact kr h c30 c31
      · have c23 := r3 h c02 c30 c01
        have c31 := r4 h c12 c11 c23
        exact kr h c30 c31
      · have c24 := r3 h c02 c30 c01
        have c31 := r4 h c12 c11 c24
        exact kr h c30 c31
      have c25 := r3 h c02 c30 c01
      have c31 := r4 h c12 c11 c25
      exact kr h c30 c31
    · exact kr h c12 c10
    have c24 := r3 h c12 c51 c11
    have c30 := r4 h c02 c01 c24
    rcases cv3 (op 1 4) with c14|c14|c14|c14|c14|c14
    · have c20 := r4 h c01 c00 c14
      have c42 := r3 h c14 c01 c10
      have c45 := r3 h c24 c12 c20
      exact kr h c42 c45
    · have c21 := r4 h c11 c14 c10
      have c13 := r3 h c21 c02 c24
      exact kr h c10 c13
    · exact kr h c14 c11
    · exact kr h c14 c10
    · exact kr h c14 c12
    rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
    · have c32 := r3 h c13 c11 c14
      exact kr h c30 c32
    · exact kr h c13 c11
    · exact kr h c13 c14
    · exact kr h c13 c10
    · exact kr h c13 c12
    have c15 := rc1 h 5 c13 c11 c14 c10 c12
    have c21 := r4 h c11 c15 c12
    have c22 := r4 h c21 c24 c10
    have c23 := r3 h c22 c02 c21
    exact kr h c23 c24
  · rcases cv5 (op 1 3) with c13|c13|c13|c13|c13|c13
    · have c20 := r4 h c01 c00 c13
      have c32 := r3 h c13 c01 c11
      have c33 := r1 h c32 c13 c20
      have c40 := r4 h c03 c02 c33
      have c50 := r4 h c04 c03 c40
      exact k1 h c50 c05 c00 c51
    · have c31 := r4 h c11 c13 c11
      have c33 := r1 h c31 c13 c11
      exact k1 h c33 c13 c31 c31
    · rcases cv5 (op 1 4) with c14|c14|c14|c14|c14|c14
      · have c20 := r4 h c01 c00 c14
        have c42 := r3 h c14 c01 c10
        have c21 := r1 h c20 c42 c00
        have c22 := r1 h c21 c02 c13
        have c30 := r4 h c02 c01 c22
        have c12 := r1 h c13 c21 c30
        exact kr h c11 c12
      · have c31 := r4 h c11 c14 c10
        exact k1 h c31 c03 c14 c31
      · exact kr h c14 c13
      · exact kr h c14 c11
      · exact kr h c14 c10
      have c44 := r3 h c14 c51 c10
      rcases cv1 (op 1 2) with c12|c12|c12|c12|c12|c12
      · have c15 := rc1 h 5 c12 c13 c11 c10 c14
        have c53 := r3 h c15 c11 c14
        exact kr h c51 c53
      · exact kr h c12 c13
      · exact kr h c12 c11
      · exact kr h c12 c10
      · exact kr h c12 c14
      have c15 := rc0 h 5 c12 c13 c11 c10 c14
      have c41 := r4 h c10 c15 c04
      exact k1 h c41 c44 c10 c44
    · exact kr h c13 c11
    · exact kr h c13 c10
    have c34 := r3 h c13 c51 c11
    rcases cv2 (op 1 4) with c14|c14|c14|c14|c14|c14
    · have c41 := r4 h c10 c14 c03
      have c43 := r1 h c41 c34 c11
      have c30 := r3 h c43 c14 c41
      exact kr h c30 c34
    · have c31 := r4 h c11 c14 c10
      exact k1 h c31 c03 c14 c31
    · exact kr h c14 c11
    · exact kr h c14 c10
    · exact kr h c14 c13
    rcases cv1 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c15 := rc1 h 5 c12 c14 c11 c10 c13
      have c41 := r4 h c10 c12 c01
      have c31 := r4 h c11 c15 c13
      have c40 := r1 h c41 c14 c12
      exact k1 h c03 c40 c31 c03
    · exact kr h c12 c14
    · exact kr h c12 c11
    · exact kr h c12 c10
    · exact kr h c12 c13
    have c15 := rc0 h 5 c12 c14 c11 c10 c13
    have c31 := r4 h c11 c12 c14
    have c43 := r4 h c31 c34 c10
    have c45 := r3 h c34 c13 c31
    have c52 := r3 h c15 c01 c13
    exact k1 h c45 c14 c52 c43
  · exact kr h c11 c10
  · rcases cv3 (op 1 4) with c14|c14|c14|c14|c14|c14
    · exact k1 h c11 c51 c14 c10
    · exact k1 h c11 c51 c14 c11
    · have c12 := r1 h c11 c51 c14
      rcases cv3 (op 1 3) with c13|c13|c13|c13|c13|c13
      · have c15 := rc3 h 5 c13 c12 c14 c10 c11
        have c20 := r4 h c01 c00 c13
        have c32 := r3 h c13 c01 c15
        exact k1 h c20 c32 c05 c20
      · exact kr h c13 c12
      · exact kr h c13 c14
      · exact kr h c13 c10
      · exact kr h c13 c11
      have c15 := rc0 h 5 c12 c14 c13 c10 c11
      have c41 := r4 h c10 c15 c04
      have c52 := r3 h c15 c01 c11
      have c45 := r4 h c51 c52 c14
      exact kr h c41 c45
    · exact kr h c14 c10
    · exact kr h c14 c11
    have c13 := r1 h c11 c51 c14
    have c35 := r3 h c13 c11 c14
    rcases cv2 (op 1 2) with c12|c12|c12|c12|c12|c12
    · have c15 := rc2 h 5 c12 c13 c14 c10 c11
      have c20 := r4 h c01 c00 c12
      have c22 := r3 h c12 c01 c15
      exact k1 h c20 c22 c05 c20
    · exact kr h c12 c13
    · exact kr h c12 c14
    · exact kr h c12 c10
    · exact kr h c12 c11
    have c15 := rc0 h 5 c13 c12 c14 c10 c11
    have c20 := r4 h c01 c00 c15
    have c52 := r3 h c15 c01 c11
    have c45 := r4 h c51 c52 c12
    have c55 := r1 h c52 c15 c20
    rcases cv5 (op 5 0) with c50|c50|c50|c50|c50|c50
    · exact k1 h c50 c05 c00 c51
    · exact kr h c50 c52
    · exact kr h c50 c55
    · exact k1 h c50 c35 c04 c55
    · exact kr h c50 c51
    exact k1 h c04 c50 c45 c02
  rcases cv5 (op 1 2) with c12|c12|c12|c12|c12|c12
  · have c41 := r4 h c10 c12 c01
    have c14 := r4 h c41 c41 c11
    exact k1 h c14 c11 c41 c11
  · exact kr h c12 c11
  · rcases cv3 (op 1 4) with c14|c14|c14|c14|c14|c14
    · have c20 := r4 h c01 c00 c14
      have c42 := r3 h c14 c01 c10
      have c21 := r1 h c20 c42 c00
      exact k1 h c12 c21 c20 c14
    · exact kr h c14 c11
    · exact kr h c14 c12
    · exact kr h c14 c10
    · have c44 := r3 h c14 c51 c10
      rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
      · exact kr h c13 c11
      · exact kr h c13 c12
      · have c15 := rc0 h 5 c11 c12 c13 c10 c14
        have c41 := r4 h c10 c15 c04
        exact k1 h c41 c44 c10 c44
      · exact kr h c13 c10
      · exact kr h c13 c14
      have c15 := rc3 h 5 c13 c11 c12 c10 c14
      have c20 := r4 h c01 c00 c13
      have c32 := r3 h c13 c01 c15
      exact k1 h c20 c32 c05 c20
    rcases cv0 (op 1 3) with c13|c13|c13|c13|c13|c13
    · exact kr h c13 c11
    · exact kr h c13 c12
    · exact kr h c13 c14
    · exact kr h c13 c10
    · have c15 := rc0 h 5 c11 c12 c14 c10 c13
      have c41 := r4 h c10 c15 c04
      have c34 := r3 h c13 c51 c14
      have c43 := r4 h c34 c34 c41
      have c44 := r4 h c41 c43 c14
      exact kr h c41 c44
    have c41 := r4 h c10 c13 c02
    have c20 := r4 h c01 c00 c13
    have c32 := r3 h c13 c01 c14
    have c25 := r1 h c20 c32 c04
    rcases cv4 (op 2 1) with c21|c21|c21|c21|c21|c21
    · exact kr h c21 c25
    · exact k1 h c12 c21 c21 c11
    · have c22 := r3 h c12 c21 c12
      exact kr h c21 c22
    · exact kr h c21 c20
    · exact k1 h c12 c21 c25 c10
    have c24 := r3 h c12 c21 c12
    have c42 := r1 h c41 c24 c12
    have c23 := r3 h c42 c14 c41
    exact k1 h c23 c12 c32 c24
  · rcases cv5 (op 1 3) with c13|c13|c13|c13|c13|c13
    · have c20 := r4 h c01 c00 c13
      have c32 := r3 h c13 c01 c12
      have c23 := r1 h c20 c32 c02
      have c33 := r1 h c32 c23 c20
      have c22 := r1 h c23 c02 c33
      exact kr h c20 c22
    · exact kr h c13 c11
    · rcases cv0 (op 1 4) with c14|c14|c14|c14|c14|c14
      · exact kr h c14 c11
      · exact kr h c14 c13
      · exact kr h c14 c12
      · exact kr h c14 c10
      · have c15 := rc0 h 5 c11 c13 c12 c10 c14
        have c52 := r3 h c15 c01 c14
        exact kr h c51 c52
      have c15 := rc5 h 5 c14 c11 c13 c12 c10
      have c41 := r4 h c10 c14 c03
      have c50 := r4 h c04 c03 c41
      exact k1 h c50 c15 c05 c50
    · exact kr h c13 c12
    · exact kr h c13 c10
    have c34 := r3 h c13 c51 c12
    have c40 := r4 h c03 c02 c34
    rcases cv0 (op 1 4) with c14|c14|c14|c14|c14|c14
    · exact kr h c14 c11
    · have c15 := rc0 h 5 c11 c14 c12 c10 c13
      have c41 := r4 h c10 c15 c04
      exact kr h c40 c41
    · exact kr h c14 c12
    · exact kr h c14 c10
    · exact kr h c14 c13
    have c41 := r4 h c10 c14 c03
    have c43 := r1 h c41 c34 c12
    have c30 := r3 h c43 c14 c41
    exact k1 h c30 c13 c05 c30
  · exact kr h c12 c10
  rcases cv2 (op 1 3) with c13|c13|c13|c13|c13|c13
  · have c20 := r4 h c01 c00 c13
    rcases cv3 (op 1 4) with c14|c14|c14|c14|c14|c14
    · exact kr h c14 c13
    · exact kr h c14 c11
    · have c15 := rc3 h 5 c13 c11 c14 c10 c12
      have c32 := r3 h c13 c01 c15
      exact k1 h c20 c32 c05 c20
    · exact kr h c14 c10
    · exact kr h c14 c12
    have c15 := rc2 h 5 c13 c11 c14 c10 c12
    have c24 := r3 h c12 c51 c15
    have c32 := r3 h c13 c01 c14
    have c25 := r1 h c20 c32 c04
    have c53 := r3 h c25 c02 c24
    exact kr h c51 c53
  · exact kr h c13 c11
  · rcases cv0 (op 1 4) with c14|c14|c14|c14|c14|c14
    · exact kr h c14 c11
    · have c15 := rc0 h 5 c11 c14 c13 c10 c12
      have c41 := r4 h c10 c15 c04
      have c24 := r3 h c12 c51 c14
      have c42 := r4 h c24 c24 c41
      have c44 := r4 h c41 c42 c14
      exact kr h c41 c44
    · exact kr h c14 c13
    · exact kr h c14 c10
    · exact kr h c14 c12
    have c15 := rc2 h 5 c14 c11 c13 c10 c12
    have c20 := r4 h c01 c00 c14
    have c24 := r3 h c12 c51 c15
    have c42 := r3 h c14 c01 c10
    have c52 := r4 h c24 c20 c42
    have c21 := r4 h c15 c12 c52
    exact k1 h c20 c42 c00 c21
  · exact kr h c13 c10
  · exact kr h c13 c12
  have c24 := r3 h c12 c51 c13
  rcases cv3 (op 1 4) with c14|c14|c14|c14|c14|c14
  · have c20 := r4 h c01 c00 c14
    have c42 := r3 h c14 c01 c10
    have c21 := r1 h c20 c42 c00
    have c22 := r1 h c21 c02 c13
    have c30 := r4 h c02 c01 c22
    exact k1 h c13 c21 c30 c12
  · exact kr h c14 c11
  · exact kr h c14 c13
  · exact kr h c14 c10
  · exact kr h c14 c12
  have c15 := rc0 h 5 c11 c13 c14 c10 c12
  have c20 := r4 h c01 c00 c15
  have c52 := r3 h c15 c01 c12
  have c23 := r1 h c20 c52 c02
  have c33 := r3 h c23 c02 c24
  have c21 := r4 h c13 c14 c33
  exact kr h c21 c24

private theorem sym8 {op : Op} (h : H op) (c00 : op 0 0 = 1) (c01 : op 0 1 = 2) (c02 : op 0 2 = 3) (c03 : op 0 3 = 4) : False := by
  rcases cv0 (op 0 4) with c04|c04|c04|c04|c04|c04
  · exact kr h c04 c00
  · exact kr h c04 c01
  · exact kr h c04 c02
  · exact kr h c04 c03
  · exact n9 h c00 c01 c02 c03 c04
  have c05 := rc5 h 5 c04 c00 c01 c02 c03
  have c10 := r4 h c00 c04 c03
  have c41 := r3 h c04 c00 c03
  rcases cv5 (op 4 0) with c40|c40|c40|c40|c40|c40
  · exact k1 h c40 c04 c00 c41
  · have c31 := r3 h c03 c40 c02
    have c13 := r1 h c10 c31 c02
    have c20 := r4 h c01 c00 c13
    have c32 := r3 h c13 c01 c10
    have c21 := r1 h c20 c32 c00
    exact k1 h c21 c02 c13 c20
  · have c32 := r3 h c03 c40 c02
    rcases cv5 (op 2 4) with c24|c24|c24|c24|c24|c24
    · exact k1 h c40 c24 c00 c41
    · have c42 := r1 h c40 c24 c01
      have c20 := r3 h c42 c04 c40
      exact k1 h c20 c02 c03 c24
    · have c23 := r4 h c32 c32 c24
      have c22 := r4 h c24 c23 c41
      have c12 := r4 h c22 c24 c23
      exact kr h c10 c12
    · have c44 := r1 h c40 c24 c03
      have c42 := r1 h c44 c04 c40
      exact k1 h c24 c32 c42 c24
    · exact k1 h c40 c24 c04 c40
    have c45 := r1 h c40 c24 c05
    rcases cv4 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c20 c02 c03 c24
    · have c11 := r3 h c01 c20 c00
      have c30 := r4 h c02 c01 c20
      have c31 := r4 h c10 c11 c00
      exact kr h c30 c31
    · have c12 := r3 h c01 c20 c00
      have c23 := r4 h c32 c32 c20
      have c22 := r4 h c20 c23 c02
      exact k1 h c12 c01 c22 c12
    · have c13 := r3 h c01 c20 c00
      have c12 := r1 h c13 c01 c32
      exact kr h c10 c12
    · exact kr h c20 c24
    have c52 := r4 h c24 c20 c45
    have c50 := r4 h c05 c05 c52
    have c42 := r1 h c45 c04 c50
    have c25 := r1 h c20 c42 c05
    have c54 := r4 h c42 c40 c25
    have c55 := r4 h c52 c50 c25
    exact k1 h c54 c55 c45 c50
  · exact kr h c40 c41
  · have c34 := r3 h c03 c40 c02
    rcases cv2 (op 4 4) with c44|c44|c44|c44|c44|c44
    · exact k1 h c40 c44 c00 c41
    · have c42 := r1 h c40 c44 c01
      have c12 := r3 h c41 c34 c44
      have c14 := r4 h c44 c40 c42
      have c23 := r3 h c12 c41 c14
      have c31 := r1 h c34 c23 c44
      exact k1 h c10 c31 c04 c10
    · exact kr h c44 c41
    · exact kr h c44 c40
    · have c45 := r1 h c40 c44 c05
      have c54 := r4 h c44 c40 c45
      have c50 := r4 h c05 c05 c54
      have c55 := r4 h c54 c50 c45
      exact kr h c54 c55
    have c43 := r1 h c40 c44 c02
    have c30 := r3 h c43 c04 c41
    have c21 := r3 h c02 c30 c01
    rcases cv5 (op 4 2) with c42|c42|c42|c42|c42|c42
    · exact kr h c42 c43
    · have c12 := r3 h c41 c34 c42
      have c11 := r1 h c12 c21 c21
      exact kr h c11 c12
    · exact kr h c42 c44
    · exact kr h c42 c41
    · exact kr h c42 c40
    have c45 := rc1 h 5 c43 c44 c41 c40 c42
    have c12 := r3 h c41 c34 c45
    have c15 := r3 h c21 c12 c21
    rcases cv0 (op 1 1) with c11|c11|c11|c11|c11|c11
    · exact kr h c11 c15
    · exact k1 h c11 c21 c11 c12
    · exact kr h c11 c10
    · have c13 := r3 h c11 c41 c15
      exact kr h c12 c13
    · exact kr h c11 c12
    have c31 := r4 h c10 c11 c00
    have c14 := r3 h c31 c03 c30
    exact k1 h c14 c01 c42 c15
  have c35 := r3 h c03 c40 c02
  rcases cv1 (op 5 0) with c50|c50|c50|c50|c50|c50
  · exact k1 h c05 c50 c50 c00
  · have c52 := r3 h c05 c50 c05
    rcases cv4 (op 5 5) with c55|c55|c55|c55|c55|c55
    · have c25 := r4 h c50 c55 c05
      have c20 := r3 h c52 c55 c50
      exact k1 h c25 c52 c55 c20
    · have c15 := r4 h c55 c52 c50
      exact k1 h c15 c01 c52 c15
    · exact kr h c55 c50
    · exact k1 h c55 c35 c52 c55
    · exact kr h c55 c52
    have c45 := r4 h c55 c52 c50
    have c42 := r1 h c45 c04 c50
    exact kr h c40 c42
  · have c53 := r1 h c50 c35 c02
    exact k1 h c05 c50 c53 c00
  · have c54 := r3 h c05 c50 c05
    have c45 := r1 h c40 c54 c05
    have c44 := r1 h c45 c04 c50
    exact kr h c40 c44
  · have c55 := r3 h c05 c50 c05
    exact kr h c50 c55
  have c51 := r3 h c05 c50 c05
  rcases cv2 (op 5 5) with c55|c55|c55|c55|c55|c55
  · have c15 := r4 h c50 c55 c05
    exact k1 h c15 c51 c55 c10
  · exact kr h c55 c50
  · have c52 := r3 h c55 c35 c51
    exact kr h c50 c52
  · have c45 := r4 h c55 c51 c50
    exact k1 h c45 c04 c50 c41
  · exact kr h c55 c51
  have c12 := r3 h c51 c55 c50
  have c25 := r4 h c55 c51 c50
  have c20 := r4 h c01 c00 c12
  have c22 := r4 h c20 c25 c05
  have c52 := r4 h c22 c20 c25
  exact kr h c51 c52

private theorem sym9 {op : Op} (h : H op) (c00 : op 0 0 = 1) (c01 : op 0 1 = 2) (c02 : op 0 2 = 3) : False := by
  rcases cv0 (op 0 3) with c03|c03|c03|c03|c03|c03
  · exact kr h c03 c00
  · exact kr h c03 c01
  · exact kr h c03 c02
  · exact sym8 h c00 c01 c02 c03
  · exact sym8 (h.cj (sw 4 5)) (cc c00) (cc c01) (cc c02) (cc c03)
  have c10 := r4 h c00 c03 c02
  have c31 := r3 h c03 c00 c02
  rcases cv5 (op 0 4) with c04|c04|c04|c04|c04|c04
  · exact kr h c04 c03
  · exact kr h c04 c00
  · exact kr h c04 c01
  · exact kr h c04 c02
  · have c05 := rc5 h 5 c03 c00 c01 c02 c04
    rcases cv3 (op 2 0) with c20|c20|c20|c20|c20|c20
    · exact k1 h c01 c20 c10 c02
    · have c30 := r4 h c02 c01 c20
      exact k1 h c30 c03 c00 c31
    · have c12 := r3 h c01 c20 c00
      have c22 := r3 h c12 c01 c10
      have c23 := r3 h c22 c02 c20
      exact kr h c22 c23
    · have c14 := r3 h c01 c20 c00
      have c21 := r4 h c10 c14 c04
      exact kr h c20 c21
    · have c15 := r3 h c01 c20 c00
      have c21 := r4 h c10 c15 c05
      exact kr h c20 c21
    have c13 := r3 h c01 c20 c00
    have c21 := r4 h c10 c13 c02
    rcases cv5 (op 2 2) with c22|c22|c22|c22|c22|c22
    · exact k1 h c21 c22 c10 c22
    · have c11 := r3 h c21 c22 c22
      exact kr h c10 c11
    · exact kr h c22 c21
    · exact kr h c22 c20
    · rcases cv5 (op 2 3) with c23|c23|c23|c23|c23|c23
      · have c32 := r4 h c20 c23 c02
        exact k1 h c31 c23 c10 c32
      · have c14 := r3 h c21 c22 c23
        have c42 := r4 h c22 c21 c23
        exact k1 h c14 c31 c42 c13
      · exact kr h c23 c21
      · exact kr h c23 c20
      · exact kr h c23 c22
      rcases cv1 (op 2 4) with c24|c24|c24|c24|c24|c24
      · have c25 := rc1 h 5 c24 c21 c20 c22 c23
        have c32 := r4 h c20 c24 c04
        have c14 := r3 h c21 c22 c25
        exact k1 h c13 c01 c32 c14
      · exact kr h c24 c21
      · exact kr h c24 c20
      · exact kr h c24 c22
      · exact kr h c24 c23
      have c25 := rc0 h 5 c24 c21 c20 c22 c23
      have c32 := r4 h c20 c25 c05
      have c53 := r4 h c32 c31 c24
      exact k1 h c25 c02 c53 c24
    rcases cv4 (op 2 3) with c23|c23|c23|c23|c23|c23
    · have c32 := r4 h c20 c23 c02
      exact k1 h c31 c23 c10 c32
    · have c15 := r3 h c21 c22 c23
      have c52 := r4 h c22 c21 c23
      exact k1 h c15 c31 c52 c13
    · exact kr h c23 c21
    · exact kr h c23 c20
    · exact kr h c23 c22
    rcases cv1 (op 2 4) with c24|c24|c24|c24|c24|c24
    · have c25 := rc1 h 5 c24 c21 c20 c23 c22
      have c32 := r4 h c20 c24 c04
      have c43 := r4 h c32 c31 c25
      exact k1 h c24 c02 c43 c25
    · exact kr h c24 c21
    · exact kr h c24 c20
    · exact kr h c24 c23
    · exact kr h c24 c22
    have c25 := rc0 h 5 c24 c21 c20 c23 c22
    have c32 := r4 h c20 c25 c05
    have c15 := r3 h c21 c22 c24
    exact k1 h c13 c01 c32 c15
  have c05 := rc4 h 5 c03 c00 c01 c02 c04
  rcases cv4 (op 3 0) with c30|c30|c30|c30|c30|c30
  · exact k1 h c30 c03 c00 c31
  · have c21 := r3 h c02 c30 c01
    have c12 := r1 h c10 c21 c01
    have c20 := r4 h c01 c00 c12
    have c22 := r1 h c21 c12 c10
    exact k1 h c22 c12 c20 c22
  · exact kr h c30 c31
  · have c23 := r3 h c02 c30 c01
    rcases cv5 (op 3 2) with c32|c32|c32|c32|c32|c32
    · have c33 := r4 h c30 c32 c01
      have c13 := r4 h c33 c30 c32
      exact kr h c10 c13
    · have c11 := r3 h c31 c23 c32
      have c13 := r4 h c32 c31 c23
      exact k1 h c13 c31 c32 c11
    · exact kr h c32 c31
    · exact kr h c32 c30
    · have c43 := r4 h c32 c31 c23
      have c34 := r4 h c43 c43 c30
      have c40 := r3 h c34 c03 c32
      have c52 := r3 h c05 c40 c04
      have c33 := r4 h c30 c34 c05
      have c53 := r4 h c33 c30 c34
      exact kr h c52 c53
    have c53 := r4 h c32 c31 c23
    have c35 := r4 h c53 c53 c30
    have c50 := r3 h c35 c03 c32
    have c33 := r4 h c30 c35 c04
    have c43 := r4 h c33 c30 c35
    have c42 := r3 h c04 c50 c05
    exact kr h c42 c43
  · have c25 := r3 h c02 c30 c01
    rcases cv5 (op 5 3) with c53|c53|c53|c53|c53|c53
    · exact k1 h c30 c53 c00 c31
    · have c32 := r1 h c30 c53 c01
      have c20 := r3 h c32 c03 c31
      exact kr h c20 c25
    · have c33 := r1 h c30 c53 c02
      have c35 := r1 h c33 c03 c30
      have c50 := r3 h c35 c33 c30
      have c55 := r1 h c50 c05 c04
      have c40 := r3 h c04 c50 c05
      exact k1 h c05 c40 c55 c00
    · exact k1 h c30 c53 c03 c30
    · have c35 := r1 h c30 c53 c04
      have c40 := r4 h c05 c04 c53
      have c50 := r3 h c35 c03 c30
      exact k1 h c04 c50 c40 c03
    have c34 := r1 h c30 c53 c05
    rcases cv2 (op 4 0) with c40|c40|c40|c40|c40|c40
    · exact k1 h c34 c03 c40 c30
    · exact k1 h c34 c03 c40 c31
    · exact k1 h c05 c40 c53 c05
    · exact k1 h c34 c03 c40 c34
    · have c50 := r4 h c04 c05 c40
      have c55 := r3 h c05 c40 c04
      exact k1 h c50 c05 c04 c55
    have c32 := r1 h c34 c03 c40
    have c52 := r3 h c05 c40 c04
    have c43 := r4 h c32 c31 c25
    have c50 := r4 h c04 c05 c43
    have c55 := r4 h c53 c50 c34
    exact kr h c52 c55
  have c24 := r3 h c02 c30 c01
  rcases cv4 (op 4 3) with c43|c43|c43|c43|c43|c43
  · exact k1 h c30 c43 c00 c31
  · have c32 := r1 h c30 c43 c01
    have c20 := r3 h c32 c03 c31
    exact kr h c20 c24
  · have c33 := r1 h c30 c43 c02
    have c34 := r1 h c33 c03 c30
    have c40 := r3 h c34 c33 c30
    have c50 := r3 h c05 c40 c04
    have c44 := r1 h c40 c04 c05
    exact k1 h c04 c50 c44 c00
  · exact k1 h c30 c43 c03 c30
  · have c34 := r1 h c30 c43 c05
    have c50 := r4 h c04 c05 c43
    have c40 := r3 h c34 c03 c30
    exact k1 h c05 c40 c50 c03
  have c35 := r1 h c30 c43 c04
  rcases cv2 (op 5 0) with c50|c50|c50|c50|c50|c50
  · have c55 := r1 h c50 c05 c04
    have c40 := r3 h c04 c50 c05
    exact k1 h c05 c40 c55 c00
  · exact k1 h c35 c03 c50 c31
  · exact k1 h c04 c50 c43 c04
  · have c44 := r3 h c04 c50 c05
    have c40 := r4 h c05 c04 c50
    exact k1 h c40 c04 c05 c44
  · exact k1 h c35 c03 c50 c35
  have c42 := r3 h c04 c50 c05
  have c32 := r1 h c35 c03 c50
  have c53 := r4 h c32 c31 c24
  have c40 := r4 h c05 c04 c53
  have c44 := r4 h c43 c40 c35
  exact kr h c42 c44

private theorem sym10 {op : Op} (h : H op) (c00 : op 0 0 = 1) (c01 : op 0 1 = 2) : False := by
  rcases cv0 (op 0 2) with c02|c02|c02|c02|c02|c02
  · exact kr h c02 c00
  · exact kr h c02 c01
  · exact sym9 h c00 c01 c02
  · exact sym9 (h.cj (sw 3 4)) (cc c00) (cc c01) (cc c02)
  · exact sym9 (h.cj (sw 3 5)) (cc c00) (cc c01) (cc c02)
  have c10 := r4 h c00 c02 c01
  have c21 := r3 h c02 c00 c01
  have c12 := r4 h c21 c21 c10
  have c11 := r4 h c10 c12 c01
  exact kr h c10 c11

private theorem sym11 {op : Op} (h : H op) (c00 : op 0 0 = 1) : False := by
  rcases cv0 (op 0 1) with c01|c01|c01|c01|c01|c01
  · exact kr h c01 c00
  · exact sym10 h c00 c01
  · exact sym10 (h.cj (sw 2 3)) (cc c00) (cc c01)
  · exact sym10 (h.cj (sw 2 4)) (cc c00) (cc c01)
  · exact sym10 (h.cj (sw 2 5)) (cc c00) (cc c01)
  have c10 := r4 h c00 c01 c00
  have c11 := r1 h c10 c01 c00
  exact k1 h c11 c01 c10 c10

/-- No operation on `Fin 6` satisfies equation 677. -/
theorem root {op : Op} (h : H op) : False := by
  rcases cv0 (op 0 0) with c00|c00|c00|c00|c00|c00
  · exact sym11 h c00
  · exact sym11 (h.cj (sw 1 2)) (cc c00)
  · exact sym11 (h.cj (sw 1 3)) (cc c00)
  · exact sym11 (h.cj (sw 1 4)) (cc c00)
  · exact sym11 (h.cj (sw 1 5)) (cc c00)
  rcases cv1 (op 0 1) with c01|c01|c01|c01|c01|c01
  · exact kr h c01 c00
  · exact sym7 h c00 c01
  · exact sym7 (h.cj (sw 2 3)) (cc c00) (cc c01)
  · exact sym7 (h.cj (sw 2 4)) (cc c00) (cc c01)
  · exact sym7 (h.cj (sw 2 5)) (cc c00) (cc c01)
  rcases cv2 (op 0 2) with c02|c02|c02|c02|c02|c02
  · exact kr h c02 c00
  · exact kr h c02 c01
  · exact sym3 h c00 c01 c02
  · exact sym3 (h.cj (sw 3 4)) (cc c00) (cc c01) (cc c02)
  · exact sym3 (h.cj (sw 3 5)) (cc c00) (cc c01) (cc c02)
  rcases cv3 (op 0 3) with c03|c03|c03|c03|c03|c03
  · exact kr h c03 c00
  · exact kr h c03 c01
  · exact kr h c03 c02
  · exact sym1 h c00 c01 c02 c03
  · exact sym1 (h.cj (sw 4 5)) (cc c00) (cc c01) (cc c02) (cc c03)
  rcases cv5 (op 0 4) with c04|c04|c04|c04|c04|c04
  · exact kr h c04 c00
  · exact kr h c04 c01
  · exact kr h c04 c02
  · exact kr h c04 c03
  · exact n1 h c00 c01 c02 c03 c04
  have c05 := rc4 h 5 c00 c01 c02 c03 c04
  rcases cv3 (op 4 0) with c40|c40|c40|c40|c40|c40
  · have c44 := r1 h c40 c04 c05
    exact kr h c40 c44
  · have c51 := r3 h c05 c40 c04
    rcases cv3 (op 5 4) with c54|c54|c54|c54|c54|c54
    · have c44 := r3 h c54 c05 c51
      exact kr h c40 c44
    · have c15 := r4 h c54 c51 c40
      have c14 := r1 h c15 c01 c51
      have c44 := r1 h c40 c14 c05
      have c10 := r1 h c14 c51 c44
      exact k1 h c01 c10 c14 c05
    · have c25 := r4 h c54 c51 c40
      rcases cv3 (op 5 0) with c50|c50|c50|c50|c50|c50
      · exact k1 h c04 c50 c40 c01
      · have c41 := r3 h c04 c50 c05
        have c12 := r3 h c41 c54 c40
        have c45 := r4 h c51 c50 c12
        have c24 := r4 h c45 c41 c50
        exact kr h c24 c25
      · exact kr h c50 c54
      · exact kr h c50 c51
      · have c45 := r3 h c04 c50 c05
        have c52 := r3 h c45 c54 c45
        exact kr h c50 c52
      have c43 := r3 h c04 c50 c05
      rcases cv3 (op 4 5) with c45|c45|c45|c45|c45|c45
      · have c55 := r3 h c45 c04 c43
        exact kr h c50 c55
      · exact kr h c45 c40
      · have c24 := r4 h c45 c43 c50
        exact kr h c24 c25
      · have c44 := r4 h c45 c43 c50
        exact k1 h c44 c04 c45 c44
      · exact kr h c45 c43
      have c32 := r3 h c43 c54 c45
      have c34 := r4 h c45 c43 c50
      have c35 := r1 h c34 c03 c43
      have c55 := r3 h c35 c43 c32
      exact kr h c54 c55
    · exact kr h c54 c51
    · have c55 := r4 h c54 c51 c40
      exact k1 h c55 c05 c54 c55
    have c35 := r4 h c54 c51 c40
    rcases cv2 (op 5 0) with c50|c50|c50|c50|c50|c50
    · exact k1 h c04 c50 c40 c01
    · have c41 := r3 h c04 c50 c05
      have c13 := r3 h c41 c54 c40
      have c45 := r4 h c51 c50 c13
      have c34 := r4 h c45 c41 c50
      exact kr h c34 c35
    · exact kr h c50 c54
    · exact kr h c50 c51
    · have c45 := r3 h c04 c50 c05
      have c53 := r3 h c45 c54 c45
      exact kr h c50 c53
    have c42 := r3 h c04 c50 c05
    rcases cv2 (op 4 5) with c45|c45|c45|c45|c45|c45
    · have c55 := r3 h c45 c04 c42
      exact kr h c50 c55
    · exact kr h c45 c40
    · have c34 := r4 h c45 c42 c50
      exact kr h c34 c35
    · have c44 := r4 h c45 c42 c50
      exact k1 h c44 c04 c45 c44
    · exact kr h c45 c42
    have c23 := r3 h c42 c54 c45
    have c24 := r4 h c45 c42 c50
    have c25 := r1 h c24 c02 c42
    have c55 := r3 h c25 c42 c23
    exact kr h c54 c55
  · have c52 := r3 h c05 c40 c04
    rcases cv3 (op 5 4) with c54|c54|c54|c54|c54|c54
    · have c44 := r3 h c54 c05 c52
      exact kr h c40 c44
    · have c15 := r4 h c54 c52 c40
      rcases cv3 (op 5 0) with c50|c50|c50|c50|c50|c50
      · exact k1 h c04 c50 c40 c02
      · exact kr h c50 c54
      · have c42 := r3 h c04 c50 c05
        have c21 := r3 h c42 c54 c40
        have c45 := r4 h c52 c50 c21
        have c14 := r4 h c45 c42 c50
        exact kr h c14 c15
      · exact kr h c50 c52
      · have c45 := r3 h c04 c50 c05
        have c51 := r3 h c45 c54 c45
        exact kr h c50 c51
      have c43 := r3 h c04 c50 c05
      rcases cv3 (op 4 5) with c45|c45|c45|c45|c45|c45
      · have c55 := r3 h c45 c04 c43
        exact kr h c50 c55
      · have c14 := r4 h c45 c43 c50
        exact kr h c14 c15
      · exact kr h c45 c40
      · have c44 := r4 h c45 c43 c50
        exact k1 h c44 c04 c45 c44
      · exact kr h c45 c43
      have c31 := r3 h c43 c54 c45
      have c34 := r4 h c45 c43 c50
      have c35 := r1 h c34 c03 c43
      have c55 := r3 h c35 c43 c31
      exact kr h c54 c55
    · have c25 := r4 h c54 c52 c40
      have c24 := r1 h c25 c02 c52
      have c44 := r1 h c40 c24 c05
      have c20 := r1 h c24 c52 c44
      exact k1 h c02 c20 c24 c05
    · exact kr h c54 c52
    · have c55 := r4 h c54 c52 c40
      exact k1 h c55 c05 c54 c55
    have c35 := r4 h c54 c52 c40
    rcases cv1 (op 5 0) with c50|c50|c50|c50|c50|c50
    · exact k1 h c04 c50 c40 c02
    · have c42 := r3 h c04 c50 c05
      have c23 := r3 h c42 c54 c40
      have c45 := r4 h c52 c50 c23
      have c34 := r4 h c45 c42 c50
      exact kr h c34 c35
    · exact kr h c50 c54
    · exact kr h c50 c52
    · have c45 := r3 h c04 c50 c05
      have c53 := r3 h c45 c54 c45
      exact kr h c50 c53
    have c41 := r3 h c04 c50 c05
    rcases cv1 (op 4 5) with c45|c45|c45|c45|c45|c45
    · have c55 := r3 h c45 c04 c41
      exact kr h c50 c55
    · exact kr h c45 c40
    · have c34 := r4 h c45 c41 c50
      exact kr h c34 c35
    · have c44 := r4 h c45 c41 c50
      exact k1 h c44 c04 c45 c44
    · exact kr h c45 c41
    have c13 := r3 h c41 c54 c45
    have c14 := r4 h c45 c41 c50
    have c15 := r1 h c14 c01 c41
    have c55 := r3 h c15 c41 c13
    exact kr h c54 c55
  · have c54 := r3 h c05 c40 c04
    have c45 := r4 h c54 c54 c40
    have c44 := r4 h c40 c45 c04
    exact kr h c40 c44
  · have c50 := r4 h c04 c05 c40
    have c55 := r3 h c05 c40 c04
    exact k1 h c50 c05 c04 c55
  have c53 := r3 h c05 c40 c04
  rcases cv2 (op 5 4) with c54|c54|c54|c54|c54|c54
  · have c44 := r3 h c54 c05 c53
    exact kr h c40 c44
  · have c15 := r4 h c54 c53 c40
    rcases cv2 (op 5 0) with c50|c50|c50|c50|c50|c50
    · exact k1 h c04 c50 c40 c03
    · exact kr h c50 c54
    · have c43 := r3 h c04 c50 c05
      have c31 := r3 h c43 c54 c40
      have c45 := r4 h c53 c50 c31
      have c14 := r4 h c45 c43 c50
      exact kr h c14 c15
    · exact kr h c50 c53
    · have c45 := r3 h c04 c50 c05
      have c51 := r3 h c45 c54 c45
      exact kr h c50 c51
    have c42 := r3 h c04 c50 c05
    rcases cv2 (op 4 5) with c45|c45|c45|c45|c45|c45
    · have c55 := r3 h c45 c04 c42
      exact kr h c50 c55
    · have c14 := r4 h c45 c42 c50
      exact kr h c14 c15
    · exact kr h c45 c40
    · have c44 := r4 h c45 c42 c50
      exact k1 h c44 c04 c45 c44
    · exact kr h c45 c42
    have c21 := r3 h c42 c54 c45
    have c24 := r4 h c45 c42 c50
    have c25 := r1 h c24 c02 c42
    have c55 := r3 h c25 c42 c21
    exact kr h c54 c55
  · have c35 := r4 h c54 c53 c40
    have c34 := r1 h c35 c03 c53
    have c44 := r1 h c40 c34 c05
    have c30 := r1 h c34 c53 c44
    exact k1 h c03 c30 c34 c05
  · exact kr h c54 c53
  · have c55 := r4 h c54 c53 c40
    exact k1 h c55 c05 c54 c55
  have c25 := r4 h c54 c53 c40
  rcases cv1 (op 5 0) with c50|c50|c50|c50|c50|c50
  · exact k1 h c04 c50 c40 c03
  · exact kr h c50 c54
  · have c43 := r3 h c04 c50 c05
    have c32 := r3 h c43 c54 c40
    have c45 := r4 h c53 c50 c32
    have c24 := r4 h c45 c43 c50
    exact kr h c24 c25
  · exact kr h c50 c53
  · have c45 := r3 h c04 c50 c05
    have c52 := r3 h c45 c54 c45
    exact kr h c50 c52
  have c41 := r3 h c04 c50 c05
  rcases cv1 (op 4 5) with c45|c45|c45|c45|c45|c45
  · have c55 := r3 h c45 c04 c41
    exact kr h c50 c55
  · have c24 := r4 h c45 c41 c50
    exact kr h c24 c25
  · exact kr h c45 c40
  · have c44 := r4 h c45 c41 c50
    exact k1 h c44 c04 c45 c44
  · exact kr h c45 c41
  have c12 := r3 h c41 c54 c45
  have c14 := r4 h c45 c41 c50
  have c15 := r1 h c14 c01 c41
  have c55 := r3 h c15 c41 c12
  exact kr h c54 c55

end E677Finite6c

theorem solution :
∀ op : Fin 6 → Fin 6 → Fin 6, ¬ FiniteMagmaE677.E677 op := by
  intro op h
  exact E677Finite6c.root (op := op) ⟨h⟩

