-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_all_killed_record_grid_prefixes_le_actual_stieltjes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:17:53.032792+00:00
-- url     : https://prove2.me/submissions/c665e9ee-5952-4cad-b391-c44dd147bd7c

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_killed_record_grid_prefix_le_actual_stieltjes

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- All killed rational-grid sampled regulator prefixes remain below the
genuine continuous-time stopped Stieltjes reward, on each sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (q : ℝ) (hq : 0 ≤ q) :
    (⨆ n : ℕ, ⨆ N : ℕ,
      let grid : ℕ → ℝ := fun j =>
        (((j : ℝ≥0) * ((n + 1 : ℕ) : ℝ≥0)⁻¹) : ℝ)
      ∑ k ∈ Finset.range N,
        if ENNReal.ofReal (grid (k + 1)) < τ then
          ENNReal.ofReal (Real.exp (-(q * grid (k + 1)))) *
            ENNReal.ofReal
              (runningSup X (grid (k + 1)).toNNReal ω -
                runningSup X (grid k).toNNReal ω)
        else 0) ≤
    (∫⁻ r in paymentTimes τ,
      if 0 < r then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) := by
  apply iSup_le
  intro n
  apply iSup_le
  intro N
  exact avram_root29_05_killed_record_grid_prefix_le_actual_stieltjes
    X ω τ q hq (n + 1) N (Nat.succ_pos n)
