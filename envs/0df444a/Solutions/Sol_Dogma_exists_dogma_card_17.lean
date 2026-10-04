-- Prove2me | solution 1 for Dogma.exists_dogma_card_17
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T05:13:00.301282+00:00
-- url     : https://prove2.me/submissions/ac766b89-a9d2-4ca0-9346-589d9fef69bf

import Mathlib

set_option autoImplicit false

namespace Dogma17

/-- The multiplication table: row `x`, column `y` is `x ⋆ y`. -/
def tbl : List (List (Fin 17)) :=
  [[0, 2, 15, 12, 13, 6, 11, 10, 7, 14, 8, 5, 3, 4, 16, 1, 9],
    [11, 1, 3, 14, 15, 16, 4, 13, 10, 0, 12, 9, 8, 7, 2, 6, 5],
    [5, 11, 2, 7, 16, 14, 9, 8, 3, 6, 13, 12, 1, 10, 0, 4, 15],
    [4, 9, 11, 3, 0, 10, 15, 6, 1, 8, 14, 16, 13, 12, 5, 7, 2],
    [12, 10, 14, 13, 4, 9, 8, 2, 16, 15, 11, 1, 0, 3, 7, 5, 6],
    [15, 13, 4, 8, 11, 5, 3, 16, 6, 12, 0, 2, 14, 1, 9, 10, 7],
    [1, 8, 13, 16, 7, 15, 6, 11, 0, 10, 9, 4, 5, 2, 3, 12, 14],
    [14, 5, 12, 11, 8, 1, 0, 7, 9, 4, 3, 10, 15, 16, 6, 2, 13],
    [9, 4, 1, 10, 2, 0, 7, 12, 8, 5, 16, 13, 6, 11, 15, 14, 3],
    [7, 14, 10, 5, 1, 11, 13, 15, 12, 9, 2, 3, 16, 6, 4, 0, 8],
    [16, 15, 6, 1, 5, 8, 2, 14, 4, 13, 10, 0, 7, 9, 12, 3, 11],
    [2, 3, 7, 6, 9, 12, 1, 0, 14, 16, 5, 11, 10, 15, 8, 13, 4],
    [13, 6, 8, 4, 3, 2, 14, 9, 5, 11, 15, 7, 12, 0, 1, 16, 10],
    [3, 16, 9, 0, 12, 7, 10, 5, 15, 2, 6, 14, 4, 13, 11, 8, 1],
    [10, 0, 16, 9, 6, 4, 5, 3, 13, 7, 1, 15, 2, 8, 14, 11, 12],
    [6, 12, 5, 2, 10, 3, 16, 4, 11, 1, 7, 8, 9, 14, 13, 15, 0],
    [8, 7, 0, 15, 14, 13, 12, 1, 2, 3, 4, 6, 11, 5, 10, 9, 16]]

def star17 (x y : Fin 17) : Fin 17 := (tbl.getD x.val []).getD y.val 0

lemma star17_rc : ∀ x y z : Fin 17, star17 x z = star17 y z → x = y := by decide +kernel

lemma star17_id : ∀ x y : Fin 17, star17 (star17 x y) y = star17 y x := by decide +kernel

end Dogma17

theorem solution : ∃ (D : Type) (star : D → D → D), Nat.card D = 17 ∧
    (∀ x y z : D, star x z = star y z → x = y) ∧ ∀ x y : D, star (star x y) y = star y x := by
  refine ⟨Fin 17, Dogma17.star17, ?_, Dogma17.star17_rc, Dogma17.star17_id⟩
  simp
