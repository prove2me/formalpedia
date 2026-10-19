-- Prove2me | solution 1 for BBCode.gross_chunk_right_back
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T10:13:20.218967+00:00
-- url     : https://prove2.me/submissions/69b0be6e-6d2a-4fdd-8bf5-49e29bfe381b

import Definitions.Def_BBCode_Setting
import Theorems.Thm_BBCode_gross_chunk_right_middle
import Theorems.Thm_BBCode_gross_chunk_right_last
open Matrix
theorem solution (v : BBCode.Qubit 12 6 → ZMod 2)
    (hv : BBCode.HX {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10)
    (ha : v (Sum.inr (0, 0)) ≠ 0)
    (hb : v (Sum.inl (3, 3)) ≠ 0 ∨ v (Sum.inr (1, 3)) ≠ 0 ∨ v (Sum.inr (2, 3)) ≠ 0) :
    ∃ u : BBCode.Qubit 12 6 → ZMod 2,
      BBCode.HX {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)} *ᵥ u = 0 ∧
      u ∈ BBCode.rowSpace (BBCode.HZ {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)}) ∧
      u (Sum.inr (0, 0)) ≠ 0 ∧ ∀ q, u q ≠ 0 → v q ≠ 0 := by
  rcases hb with h0 | h1 | h2
  · apply BBCode.gross_chunk_right_middle v hv hw ha
    exact Or.inl h0
  · apply BBCode.gross_chunk_right_middle v hv hw ha
    exact Or.inr h1
  · apply BBCode.gross_chunk_right_last v hv hw ha
    exact h2

#print axioms solution
