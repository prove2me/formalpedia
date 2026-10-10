-- Prove2me | solution 1 for BookProof.ChapterLpRestrictSplit.restrictEmbed_coeFn
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:24:29.996211+00:00
-- url     : https://prove2.me/submissions/c0943977-a775-464b-85a1-783cf5597c7f

-- Generated from ChapterLpRestrictSplit.lean — solution of BookProof.ChapterLpRestrictSplit.restrictEmbed_coeFn
import Mathlib
import Definitions.Def_ChapterLpRestrictSplit
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLpRestrictSplit



noncomputable section

open MeasureTheory


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

variable {α : Type*} [MeasurableSpace α] {mu : Measure α}

set_option maxHeartbeats 1000000 in
theorem solution {A : Set α} (hA : MeasurableSet A) (u : Lp ℂ 2 (mu.restrict A)) :
    (restrictEmbed hA u : α → ℂ) =ᵐ[mu] A.indicator (u : α → ℂ) := (memLp_indicator_of_restrict hA u).coeFn_toLp
