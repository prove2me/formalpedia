-- Prove2me | solution 1 for BookProof.ChapterF1.bargmann_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:55:37.663985+00:00
-- url     : https://prove2.me/submissions/9c01ea34-bdc7-473d-b867-77a47bb514b4

-- Generated from ChapterF1.lean — solution of BookProof.ChapterF1.bargmann_eq_sum
import Mathlib
import Definitions.Def_ChapterF1
open BookProof.ChapterF1



open Polynomial Finset
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (p q : ℂ[X]) {s : Finset ℕ}
    (hp : p.support ⊆ s) (hq : q.support ⊆ s) :
    bargmann p q = ∑ n ∈ s, (n.factorial : ℂ) * (starRingEnd ℂ) (p.coeff n) * q.coeff n := by

  convert Finset.sum_subset ( Finset.union_subset hp hq ) _ using 1
  all_goals first
    | aesop
    | (intro x _ hnp; simp_all [Finset.mem_union, Polynomial.mem_support_iff])
