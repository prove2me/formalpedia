-- Prove2me | solution 1 for BookProof.ChapterF1.ccr
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:54:45.301984+00:00
-- url     : https://prove2.me/submissions/4f233b36-7d2a-40a5-9f9a-01fb9af2e3fc

-- Generated from ChapterF1.lean — solution of BookProof.ChapterF1.ccr
import Mathlib
import Definitions.Def_ChapterF1
open BookProof.ChapterF1



open Polynomial Finset
open scoped BigOperators


noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution : annih ∘ₗ creat - creat ∘ₗ annih = LinearMap.id := by

  refine LinearMap.ext fun p => ?_
  change derivative (X * p) - X * derivative p = p
  simp [derivative_mul]
