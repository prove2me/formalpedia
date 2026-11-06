-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_original_bounded_stop_negative_band_nonvoid_probability_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T10:24:18.466105+00:00
-- url     : https://prove2.me/submissions/1cbc7530-8f55-485a-9fae-c13bc8de842b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f2_original_negative_band_nonvoid_second_order_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped-band jump probability is bounded by the deterministic rate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ)
    (τ : Ω → ℝ≥0) (hτ : ∀ ω, τ ω ≤ T) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    P.real {ω : Ω | K ω ≠ 0} ≤ r := by
  classical
  let K : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ τ ω ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let KT : Ω → ℕ := fun ω =>
    {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}.ncard
  let r : ℝ :=
    ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
  change P.real {ω : Ω | K ω ≠ 0} ≤ r
  have hKle (ω : Ω) : K ω ≤ KT ω := by
    apply Set.ncard_le_ncard
    · intro u hu
      exact ⟨hu.1, (hu.2.1).trans (hτ ω), hu.2.2⟩
    · exact avram_wave7_06_original_negative_band_marked_times_finite X ω T n
  have hsubset : {ω : Ω | K ω ≠ 0} ⊆ {ω : Ω | KT ω ≠ 0} := by
    intro ω hω
    have hKpos : 0 < K ω := Nat.pos_of_ne_zero hω
    have hKTpos : 0 < KT ω := lt_of_lt_of_le hKpos (hKle ω)
    exact Nat.ne_of_gt hKTpos
  have hprob : P.real {ω : Ω | K ω ≠ 0} ≤
      P.real {ω : Ω | KT ω ≠ 0} := by
    exact ENNReal.toReal_mono
      (measure_ne_top P {ω : Ω | KT ω ≠ 0})
      (measure_mono hsubset)
  have hfixed :=
    avram_p4_f2_original_negative_band_nonvoid_second_order_bound X T n
  change r - r ^ 2 / 2 ≤ P.real {ω : Ω | KT ω ≠ 0} ∧
    P.real {ω : Ω | KT ω ≠ 0} ≤ r at hfixed
  exact hprob.trans hfixed.2
