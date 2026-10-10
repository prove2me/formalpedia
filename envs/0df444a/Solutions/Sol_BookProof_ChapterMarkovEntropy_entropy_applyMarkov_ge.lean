-- Prove2me | solution 1 for BookProof.ChapterMarkovEntropy.entropy_applyMarkov_ge
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:47:27.939+00:00
-- url     : https://prove2.me/submissions/185a4912-d90c-420a-9bbb-6237805439a6

-- Generated from ChapterMarkovEntropy.lean — solution of BookProof.ChapterMarkovEntropy.entropy_applyMarkov_ge
import Mathlib
import Definitions.Def_ChapterMarkovEntropy
import Theorems.Thm_BookProof_ChapterDutchBook_Coherent_nonneg
import Definitions.Def_ChapterIrreversible
open BookProof.ChapterMarkovEntropy



open scoped BigOperators
open Finset


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (M : Fin n → Fin n → ℝ) (hM : IsDoublyStochastic M)
    (p : Fin n → ℝ) (hp : ∀ i, 0 ≤ p i) :
    entropy p ≤ entropy (applyMarkov M p) := by

  -- Row-wise concave Jensen inequality for `negMulLog`, weights `M j i`.
  have h_jensen : ∀ j, ∑ i, M j i * Real.negMulLog (p i)
      ≤ Real.negMulLog (∑ i, M j i * p i) := by
    intro j
    have h := Real.concaveOn_negMulLog.le_map_sum (t := Finset.univ)
      (w := fun i => M j i) (p := fun i => p i)
      (fun i _ => hM.nonneg j i) (hM.rowSum j)
      (fun i _ => Set.mem_Ici.mpr (hp i))
    simpa [smul_eq_mul] using h
  calc entropy p
      = ∑ i, (∑ j, M j i) * Real.negMulLog (p i) := by simp [entropy, hM.colSum]
    _ = ∑ j, ∑ i, M j i * Real.negMulLog (p i) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    _ ≤ ∑ j, Real.negMulLog (∑ i, M j i * p i) :=
        Finset.sum_le_sum fun j _ => h_jensen j
    _ = entropy (applyMarkov M p) := rfl
