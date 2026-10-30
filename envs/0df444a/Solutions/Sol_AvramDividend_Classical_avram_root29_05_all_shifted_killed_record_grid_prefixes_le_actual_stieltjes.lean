-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_all_shifted_killed_record_grid_prefixes_le_actual_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T15:54:57.675024+00:00
-- url     : https://prove2.me/submissions/f858d103-6140-4e1a-9d83-f57dc920b991

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_killed_record_grid_prefix_le_actual_stieltjes
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- Every strictly killed sampled future-record cash prefix is dominated
by the actual continuous-time shifted Stieltjes regulator reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (age : ℝ≥0)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) :
    let M : ℝ≥0 → ℝ := fun v =>
      sSup ((fun w : ℝ≥0 => X.X (age + w) ω - X.X age ω) '' Icc 0 v)
    let μ : Measure ℝ := dividendMeasure (fun r (_ : Ω) => M r) ω
    (⨆ n : ℕ, ⨆ N : ℕ,
      let grid : ℕ → ℝ := fun j =>
        (((j : ℝ≥0) * ((n + 1 : ℕ) : ℝ≥0)⁻¹) : ℝ)
      ∑ k ∈ Finset.range N,
        if ENNReal.ofReal (grid (k + 1)) < τ then
          ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
            ENNReal.ofReal
              (M (grid (k + 1)).toNNReal - M (grid k).toNNReal)
        else 0) ≤
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0 ∂μ) := by
  apply iSup_le
  intro n
  apply iSup_le
  intro N
  exact avram_root29_05_shifted_killed_record_grid_prefix_le_actual_stieltjes
    X ω age τ q hq (n + 1) N (Nat.succ_pos n)
