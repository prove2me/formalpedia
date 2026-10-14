-- Prove2me | solution 2 for BookProof.ChapterEulerNState.euler_sum_one
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T12:40:55.714036+00:00
-- url     : https://prove2.me/submissions/474a3c93-1c8b-45eb-9b84-2c0e76672ee8

-- Generated from ChapterEulerNState.lean — theorem BookProof.ChapterEulerNState.euler_sum_one
import Mathlib
import Definitions.Def_ChapterEulerNState
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterEulerNState


open scoped BigOperators
open BookProof.ChapterEulerNState

theorem solution(θ : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, bornProb θ n k = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ]
  have h1 : ∀ k ∈ Finset.range m, BookProof.ChapterEulerNState.bornProb θ (m + 1) k = tailProd θ k - tailProd θ (k + 1) := by
    intro k hk
    rw [Finset.mem_range] at hk
    unfold BookProof.ChapterEulerNState.bornProb tailProd
    rw [if_pos (by omega), Finset.prod_range_succ, Real.cos_sq']
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_range_sub']
  unfold BookProof.ChapterEulerNState.bornProb
  rw [if_neg (by omega), if_pos rfl]
  simp [tailProd]
