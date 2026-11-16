-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_original_uniform_source_physical_drift_only_nonconvergence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:12:08.324752+00:00
-- url     : https://prove2.me/submissions/edb1bebc-d84e-4bb5-a63c-ed46083a24f8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_nojump_tenth_clipped_cash_plus_terminal_lower
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_linear_zero_barrier_physical_L_vanish
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_tenth_clipped_cash_positivepart_cannot_vanish
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift) :
    let D := barrierStrategy X 0 0
    let T : ℝ := 1 / 10
    let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
    let u : ℕ → ℕ → ℝ≥0 := fun n i =>
      ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
    let F : ℕ → ℝ := fun n =>
      (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩
          Iio (T - T / ((n : ℝ) + 2)),
        ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
        (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) < ruinTime X 0 D ω then
          Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω)
         else 0)
    let L : ℕ → ℝ := fun n =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω - rightLimit D t ω) (u n i)
      ∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < (1 : ℝ≥0∞) then
          Real.exp (-(u n i : ℝ)) *
            (X.drift * deriv w (Z i) - w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0
    ¬ Tendsto (fun n => max (F n - (w 0 + L n)) 0)
      atTop (𝓝 (0 : ℝ)) := by
  dsimp
  let D := barrierStrategy X 0 0
  let T : ℝ := 1 / 10
  let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
  let u : ℕ → ℕ → ℝ≥0 := fun n i =>
    ⟨(1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
  let F : ℕ → ℝ := fun n =>
    (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩
        Iio (T - T / ((n : ℝ) + 2)),
      ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
      (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) < ruinTime X 0 D ω then
        Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω)
       else 0)
  let L : ℕ → ℝ := fun n =>
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => (0 : ℝ) + X.X t ω - rightLimit D t ω) (u n i)
    ∑ i ∈ Finset.range (n + 1),
      if (u n i : ℝ≥0∞) < ruinTime X 0 D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < (1 : ℝ≥0∞) then
        Real.exp (-(u n i : ℝ)) *
          (X.drift * deriv w (Z i) - w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ)) else 0
  have hCash : ∀ n, 4 ≤ n →
      (2 / 25 + 1 / 2 : ℝ) * Real.exp (-T) ≤ F n := by
    intro n hn
    simpa only [F, D, T, w] using
      (avram_bvb_obstruction_original_nojump_tenth_clipped_cash_plus_terminal_lower
        X ω hDrift hPath n hn)
  have hLedger : ∀ n, L n = 0 := by
    intro n
    have hWithin : ∀ i ∈ Finset.range (n + 1), u n i ≤ 1 := by
      intro i hi
      change (1 / 10 : ℝ) * (i : ℝ) / ((n : ℝ) + 2) ≤ 1
      have hIndex : (i : ℝ) ≤ n := by
        exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hDenom : 0 < (n : ℝ) + 2 := by positivity
      apply (div_le_iff₀ hDenom).2
      nlinarith
    simpa only [L, D, one_mul] using
      (avram_bvb_obstruction_original_linear_zero_barrier_physical_L_vanish
        X ω hDrift hPath u n hWithin w 1 (1 : ℝ≥0∞))
  have hGap := avram_bvb_obstruction_tenth_clipped_cash_positivepart_cannot_vanish
    F L (by simpa only [T] using hCash) hLedger
  change ¬ Tendsto (fun n => max (F n - (w 0 + L n)) 0)
    atTop (𝓝 (0 : ℝ))
  simpa [w] using hGap
