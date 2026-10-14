-- Prove2me | solution 2 for BookProof.ChapterEulerNState.euler_wave_unit
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-13T10:49:12.644442+00:00
-- url     : https://prove2.me/submissions/803080fa-0c68-4d44-9b6b-d4570e6421ea

-- Generated from ChapterEulerNState.lean — theorem BookProof.ChapterEulerNState.euler_wave_unit
import Mathlib
import Definitions.Def_ChapterEulerNState
import Definitions.Def_ChapterDoubleSlit
open BookProof.ChapterDoubleSlit
open BookProof.ChapterEulerNState


open scoped BigOperators
open BookProof.ChapterEulerNState

theorem solution(θ : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) :
    ∑ k ∈ Finset.range n, (eulerWave θ n k) ^ 2 = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Finset.sum_range_succ]
  have h1 : ∀ k ∈ Finset.range m, eulerWave θ (m + 1) k ^ 2 = (∏ i ∈ Finset.range k, Real.sin (θ i) ^ 2) - ∏ i ∈ Finset.range (k + 1), Real.sin (θ i) ^ 2 := by
    intro k hk
    rw [Finset.mem_range] at hk
    unfold eulerWave
    rw [if_pos (by omega), Finset.prod_range_succ, mul_pow, Finset.prod_pow, Real.cos_sq']
    ring
  rw [Finset.sum_congr rfl h1, Finset.sum_range_sub']
  simp only [Finset.prod_range_zero]
  unfold eulerWave
  rw [if_neg (by omega), if_pos rfl, ← Finset.prod_pow]
  ring
