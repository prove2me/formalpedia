-- Prove2me | solution 1 for AvramDividend.Classical.nnreal_bounded_stopping_delay_preserves_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T11:27:19.094347+00:00
-- url     : https://prove2.me/submissions/5a59ca2a-8801-4689-aa4a-502a249ca56a

import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal
theorem solution
    {Ω : Type*} (τ : Ω → ℝ≥0) (T h : ℝ≥0)
    (hbounded : ∀ ω, τ ω ≤ T) :
    ∀ ω, τ ω + h ≤ T + h := fun ω => add_le_add_left (hbounded ω) h
