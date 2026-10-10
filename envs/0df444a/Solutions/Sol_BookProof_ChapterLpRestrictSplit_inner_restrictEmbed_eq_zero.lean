-- Prove2me | solution 1 for BookProof.ChapterLpRestrictSplit.inner_restrictEmbed_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:25:13.464918+00:00
-- url     : https://prove2.me/submissions/90d04784-bd42-4340-b3b4-8394cb3d4ceb

-- Generated from ChapterLpRestrictSplit.lean — solution of BookProof.ChapterLpRestrictSplit.inner_restrictEmbed_eq_zero
import Mathlib
import Definitions.Def_ChapterLpRestrictSplit
import Theorems.Thm_BookProof_ChapterLpRestrictSplit_restrictEmbed_coeFn
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit



noncomputable section

open MeasureTheory


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution {A B : Set α} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : Disjoint A B) (u : Lp ℂ 2 (mu.restrict A)) (v : Lp ℂ 2 (mu.restrict B)) :
    inner ℂ (restrictEmbed hA u) (restrictEmbed hB v) = 0 := by

  rw [L2.inner_def]
  have : ∀ᵐ x ∂mu, (inner ℂ ((restrictEmbed hA u : α → ℂ) x)
      ((restrictEmbed hB v : α → ℂ) x) : ℂ) = 0 := by
    filter_upwards [restrictEmbed_coeFn hA u, restrictEmbed_coeFn hB v] with x h1 h2
    rw [h1, h2]
    by_cases hxA : x ∈ A
    · have hxB : x ∉ B := Set.disjoint_left.1 hAB hxA
      simp [Set.indicator_of_notMem hxB]
    · simp [Set.indicator_of_notMem hxA]
  rw [integral_congr_ae this]
  simp
