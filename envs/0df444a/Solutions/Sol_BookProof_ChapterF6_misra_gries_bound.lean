-- Prove2me | solution 1 for BookProof.ChapterF6.misra_gries_bound
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:06:51.059364+00:00
-- url     : https://prove2.me/submissions/a4bd4247-519f-4bcd-9794-c860f8e0ef72

-- Generated from ChapterF6.lean — solution of BookProof.ChapterF6.misra_gries_bound
import Mathlib
import Definitions.Def_ChapterF6
import Theorems.Thm_BookProof_ChapterF6_mg_upper
import Theorems.Thm_BookProof_ChapterF6_mg_lower
import Theorems.Thm_BookProof_ChapterF6_mgD_bound
open BookProof.ChapterF6



open scoped BigOperators


variable {α : Type*} [DecidableEq α]

variable {α : Type*} [DecidableEq α]

set_option maxHeartbeats 1000000 in
theorem solution (k : ℕ) (hk : 1 ≤ k) (s : List α) (x : α) :
    s.count x - s.length / k ≤ (mg k s) x ∧ (mg k s) x ≤ s.count x := by

  refine ⟨ Nat.sub_le_of_le_add ?_, ?_ ⟩
  · convert mg_lower k s x |> le_trans <| Nat.add_le_add_left _ _ using 1;
    exact Nat.le_div_iff_mul_le hk |>.2 ( by linarith [ mgD_bound k s ] );
  · exact mg_upper k s x
