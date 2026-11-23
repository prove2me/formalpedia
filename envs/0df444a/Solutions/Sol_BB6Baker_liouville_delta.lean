-- Prove2me | solution 1 for BB6Baker.liouville_delta
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T18:08:23.551801+00:00
-- url     : https://prove2.me/submissions/cb92d70b-b9f2-4827-be34-c92b7866c949

import Mathlib
import Definitions.Def_BB6Delta

theorem solution (N b1' b3' b2'' b3'' α1 α2 α3 : ℕ) (kml rst : Fin N → ℕ × ℕ × ℕ)
    (h : BB6Delta.deltaR N b1' b3' b2'' b3'' α1 α2 α3 kml rst ≠ 0) :
    BB6Delta.deltaR N b1' b3' b2'' b3'' α1 α2 α3 kml rst =
        (BB6Delta.deltaZ N b1' b3' b2'' b3'' α1 α2 α3 kml rst : ℝ) ∧
      1 ≤ |BB6Delta.deltaR N b1' b3' b2'' b3'' α1 α2 α3 kml rst| := by
  have key : BB6Delta.deltaR N b1' b3' b2'' b3'' α1 α2 α3 kml rst =
      (BB6Delta.deltaZ N b1' b3' b2'' b3'' α1 α2 α3 kml rst : ℝ) := by
    unfold BB6Delta.deltaR BB6Delta.deltaZ
    rw [Int.cast_det]
    congr 1
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, BB6Delta.entryNat]
    push_cast
    ring
  refine ⟨key, ?_⟩
  rw [key] at h ⊢
  have hz : BB6Delta.deltaZ N b1' b3' b2'' b3'' α1 α2 α3 kml rst ≠ 0 := by
    intro h0
    apply h
    rw [h0]
    simp
  have h1 := Int.one_le_abs hz
  have h2 : ((1 : ℤ) : ℝ) ≤ ((|BB6Delta.deltaZ N b1' b3' b2'' b3'' α1 α2 α3 kml rst| : ℤ) : ℝ) := by
    exact_mod_cast h1
  push_cast at h2
  exact h2
