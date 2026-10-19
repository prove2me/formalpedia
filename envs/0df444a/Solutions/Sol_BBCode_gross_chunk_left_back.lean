-- Prove2me | solution 1 for BBCode.gross_chunk_left_back
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T10:08:00.289973+00:00
-- url     : https://prove2.me/submissions/15a6f16c-d8e0-4dfb-977b-f4d4befe9a5c

import Definitions.Def_BBCode_Setting
import Theorems.Thm_BBCode_gross_chunk_left_middle
import Theorems.Thm_BBCode_gross_chunk_left_last
open Matrix
theorem solution (v : BBCode.Qubit 12 6 → ZMod 2)
    (hv : BBCode.HX {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)} *ᵥ v = 0)
    (hw : BBCode.weight v ≤ 10)
    (ha : v (Sum.inl (0, 0)) ≠ 0)
    (hb : v (Sum.inr (0, 1)) ≠ 0 ∨ v (Sum.inr (1, 4)) ≠ 0 ∨ v (Sum.inr (2, 4)) ≠ 0) :
    ∃ u : BBCode.Qubit 12 6 → ZMod 2,
      BBCode.HX {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)} *ᵥ u = 0 ∧
      u ∈ BBCode.rowSpace (BBCode.HZ {(3,0),(0,1),(0,2)} {(0,3),(1,0),(2,0)}) ∧
      u (Sum.inl (0, 0)) ≠ 0 ∧ ∀ q, u q ≠ 0 → v q ≠ 0 := by
  rcases hb with h0 | h1 | h2
  · apply BBCode.gross_chunk_left_middle v hv hw ha
    exact Or.inl h0
  · apply BBCode.gross_chunk_left_middle v hv hw ha
    exact Or.inr h1
  · apply BBCode.gross_chunk_left_last v hv hw ha
    exact h2

#print axioms solution
