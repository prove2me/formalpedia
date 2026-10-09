-- Prove2me | solution 1 for BookProof.ChapterF2.massGap_smallest_excited
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:59:18.802043+00:00
-- url     : https://prove2.me/submissions/0a96892e-d334-466e-ae11-7b1581419abd

-- Generated from ChapterF2.lean — solution of BookProof.ChapterF2.massGap_smallest_excited
import Mathlib
import Definitions.Def_ChapterF2
import Theorems.Thm_BookProof_ChapterF1_numberOp_monomial
open BookProof.ChapterF2



open Polynomial Finset
open scoped BigOperators


open BookProof.ChapterF1

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (hn : n ≠ 0) :
    hamiltonian (X ^ n) = (n : ℂ) • X ^ n ∧ (1 : ℕ) ≤ n := ⟨numberOp_monomial n, Nat.one_le_iff_ne_zero.mpr hn⟩
