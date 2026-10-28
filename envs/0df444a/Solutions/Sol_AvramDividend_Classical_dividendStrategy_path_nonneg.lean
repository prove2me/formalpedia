-- Prove2me | solution 1 for AvramDividend.Classical.dividendStrategy_path_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:01:11.501456+00:00
-- url     : https://prove2.me/submissions/8076f4c5-5cb4-4169-ba75-65c97f32f6cc

import Mathlib.Data.NNReal.Defs
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- A cumulative dividend strategy starts at zero and is nondecreasing, so its payout path is everywhere nonnegative. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (t : ℝ≥0) :
    0 ≤ D t ω := by
  have h : D 0 ω ≤ D t ω :=
    (hD.2.1 ω) (show (0 : ℝ≥0) ≤ t from by exact zero_le)
  simpa only [hD.1 ω] using h
