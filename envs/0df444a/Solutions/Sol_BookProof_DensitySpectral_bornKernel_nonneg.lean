-- Prove2me | solution 1 for BookProof.DensitySpectral.bornKernel_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-08T23:49:26.002472+00:00
-- url     : https://prove2.me/submissions/0884136f-f5a7-4c2c-a763-7677d635e019

-- Generated from ChapterDensityMarginalConditional.lean — solution of BookProof.DensitySpectral.bornKernel_nonneg
import Mathlib
import Definitions.Def_ChapterDensityMarginalConditional
open BookProof.DensitySpectral




open Matrix
open scoped BigOperators ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

variable {n : Type*} [Fintype n] [DecidableEq n]

set_option maxHeartbeats 1000000 in
omit [Fintype n] [DecidableEq n] in
theorem solution (U : Matrix n n ℂ) (i j : n) : 0 ≤ bornKernel U i j := Complex.normSq_nonneg _
