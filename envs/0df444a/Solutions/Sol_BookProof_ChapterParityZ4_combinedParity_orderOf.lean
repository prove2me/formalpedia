-- Prove2me | solution 1 for BookProof.ChapterParityZ4.combinedParity_orderOf
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T00:12:25.777983+00:00
-- url     : https://prove2.me/submissions/2a9bde0b-00d5-408b-8f54-372258247b39

-- Generated from ChapterParityZ4.lean — solution of BookProof.ChapterParityZ4.combinedParity_orderOf
import Mathlib
import Definitions.Def_ChapterParityZ4
import Theorems.Thm_BookProof_ChapterParityZ4_combinedParity_sq_ne_one
import Theorems.Thm_BookProof_ChapterParityZ4_combinedParity_pow_four
import Definitions.Def_ChapterParity
import Definitions.Def_ChapterParityQL
import Definitions.Def_ChapterA3
open BookProof.ChapterParityZ4



open Matrix


open BookProof.ChapterParity
open BookProof.ChapterParityQL
open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : orderOf combinedParity = 4 := by

  have h_order : combinedParity ^ 4 = 1 ∧ combinedParity ^ 2 ≠ 1 := by
    exact ⟨ combinedParity_pow_four, combinedParity_sq_ne_one ⟩;
  rw [ orderOf_eq_of_pow_and_pow_div_prime ];
  · decide;
  · exact h_order.1;
  · intro p pp dp
    have hle := Nat.le_of_dvd ( by decide ) dp
    interval_cases p <;> first
      | exact absurd pp ( by decide )
      | exact absurd dp ( by decide )
      | simpa using h_order.2
