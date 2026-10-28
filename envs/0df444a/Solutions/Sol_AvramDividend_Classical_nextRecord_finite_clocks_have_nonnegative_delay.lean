-- Prove2me | solution 1 for AvramDividend.Classical.nextRecord_finite_clocks_have_nonnegative_delay
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T23:05:28.252836+00:00
-- url     : https://prove2.me/submissions/7e0a2dd9-a8db-4950-a35e-91f6eff71062

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Mathlib.Data.ENNReal.Basic
import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (b ε : ℝ) (hε : 0 ≤ ε) (u v : ℝ≥0)
    (hu : (u : ℝ≥0∞) = twoSidedExitUpTime X b ω)
    (hv : (v : ℝ≥0∞) = twoSidedExitUpTime X (b + ε) ω) :
    ∃ δ : ℝ≥0, u + δ = v := by 
  have h := twoSidedExitUpTime_mono_threshold X b (b + ε) (by linarith) ω
  rw [← hu, ← hv, ENNReal.coe_le_coe] at h
  exact ⟨v - u, add_tsub_cancel_of_le h⟩
