-- Prove2me | solution 1 for BookProof.ChapterLpRestrictSplit.restrictEmbed_add_restrictEmbed_compl
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:24:48.447865+00:00
-- url     : https://prove2.me/submissions/73835820-20f6-4629-9d9f-050cd2dbc088

-- Generated from ChapterLpRestrictSplit.lean — solution of BookProof.ChapterLpRestrictSplit.restrictEmbed_add_restrictEmbed_compl
import Mathlib
import Definitions.Def_ChapterLpRestrictSplit
import Theorems.Thm_BookProof_ChapterLpRestrictSplit_restrictEmbed_restrictProj_coeFn
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit



noncomputable section

open MeasureTheory


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution {A : Set α} (hA : MeasurableSet A)
    (u : Lp ℂ 2 mu) :
    restrictEmbed hA (restrictProj A u) + restrictEmbed hA.compl (restrictProj Aᶜ u) = u := by

  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_add (restrictEmbed hA (restrictProj A u))
      (restrictEmbed hA.compl (restrictProj Aᶜ u)),
    restrictEmbed_restrictProj_coeFn hA u,
    restrictEmbed_restrictProj_coeFn hA.compl u] with x h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]
  by_cases hxA : x ∈ A <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hxA]
