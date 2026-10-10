-- Prove2me | solution 1 for BookProof.ChapterLinftyMaximalAbelian.multOp_indicator_oneLp
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T15:35:46.06886+00:00
-- url     : https://prove2.me/submissions/f2d499c3-65a0-4b72-9a40-d8980ef48fb0

-- Generated from ChapterLinftyMaximalAbelian.lean — solution of BookProof.ChapterLinftyMaximalAbelian.multOp_indicator_oneLp
import Mathlib
import Definitions.Def_ChapterLinftyMaximalAbelian
import Theorems.Thm_BookProof_ChapterLinftyMaximalAbelian_oneLp_coeFn
import Theorems.Thm_BookProof_ChapterLinftyMultiplication_multOp_coeFn
import Definitions.Def_ChapterLinftyMultiplication
open BookProof.ChapterLinftyMaximalAbelian



noncomputable section

open MeasureTheory ENNReal Complex


open BookProof.ChapterLinftyMultiplication

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

set_option maxHeartbeats 1000000 in
theorem solution {s : Set α} (hs : MeasurableSet s) (c : ℂ) :
    multOp (s.indicator fun _ => c) ((memLp_top_const c).indicator hs) (oneLp μ)
      = indicatorConstLp 2 hs (measure_ne_top μ s) c := by

  refine Lp.ext ?_
  filter_upwards [multOp_coeFn (s.indicator fun _ => c) ((memLp_top_const c).indicator hs)
      (oneLp μ), oneLp_coeFn (μ := μ),
    indicatorConstLp_coeFn (p := (2 : ℝ≥0∞)) (hs := hs) (hμs := measure_ne_top μ s) (c := c)]
    with x h1 h2 h3
  rw [h1, h2, h3, mul_one]
