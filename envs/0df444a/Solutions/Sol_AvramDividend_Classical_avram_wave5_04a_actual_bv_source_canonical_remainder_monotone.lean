-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04a_actual_bv_source_canonical_remainder_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:28:52.454118+00:00
-- url     : https://prove2.me/submissions/dc8fe616-2172-49d3-855f-100bbf73bd1a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- The actual BV downward finite-variation remainder is one coherent,
nondecreasing original-process path after subtracting every source left jump.
No pure-jump equality or independent Poisson realisation is imposed. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P,
      Monotone (fun t : ℝ≥0 =>
        ((t : ℝ) * X.drift - X.X t ω) -
          (∑' (u : ℝ≥0),
            if 0 < u ∧ u ≤ t then
              ENNReal.ofReal (Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u - X.X u ω)
            else 0).toReal) := by
  filter_upwards
    [avram_wave5_04a_actual_bv_interval_source_jump_real_nonnegative_remainder X hBV,
      avram_wave4_04a_bv_actual_interval_total_jump_magnitudes_le_residual X hBV]
    with ω hreal hjumps
  classical
  let S (t : ℝ≥0) : ℝ := (t : ℝ) * X.drift - X.X t ω
  let jump (v : ℝ≥0) : ℝ≥0∞ :=
    ENNReal.ofReal (Function.leftLim
      (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
  let mass (a b : ℝ≥0) : ℝ≥0∞ :=
    ∑' (v : ℝ≥0), if a < v ∧ v ≤ b then jump v else 0
  have hmass_le (a b : ℝ≥0) (hab : a ≤ b) :
      mass a b ≤ ENNReal.ofReal (S b - S a) := by
    simpa only [mass, jump, S] using hjumps a b hab
  have hmass_finite (a b : ℝ≥0) (hab : a ≤ b) :
      mass a b ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmass_le a b hab)
  have hreal_interval (a b : ℝ≥0) (hab : a ≤ b) :
      ∃ r : ℝ, 0 ≤ r ∧ (mass a b).toReal + r = S b - S a := by
    simpa only [mass, jump, S] using hreal a b hab
  change Monotone (fun t : ℝ≥0 => S t - (mass 0 t).toReal)
  intro s t hst
  have hpoint (v : ℝ≥0) :
      (if 0 < v ∧ v ≤ t then jump v else 0) =
      (if 0 < v ∧ v ≤ s then jump v else 0) +
        (if s < v ∧ v ≤ t then jump v else 0) := by
    by_cases hvs : v ≤ s
    · have hvt : v ≤ t := hvs.trans hst
      have hno : ¬ s < v := not_lt.mpr hvs
      by_cases hp : 0 < v
      · simp [hp, hvs, hvt, hno]
      · simp [hp, hno]
    · have hsv : s < v := lt_of_not_ge hvs
      have hp : 0 < v := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hsv
      by_cases hvt : v ≤ t
      · simp [hp, hvs, hsv, hvt]
      · simp [hp, hvs, hsv, hvt]
  have hmass_split : mass 0 t = mass 0 s + mass s t := by
    change tsum (fun v : ℝ≥0 =>
      if 0 < v ∧ v ≤ t then jump v else 0) =
        tsum (fun v : ℝ≥0 => if 0 < v ∧ v ≤ s then jump v else 0) +
          tsum (fun v : ℝ≥0 => if s < v ∧ v ≤ t then jump v else 0)
    calc
      tsum (fun v : ℝ≥0 => if 0 < v ∧ v ≤ t then jump v else 0) =
          tsum (fun v : ℝ≥0 =>
            (if 0 < v ∧ v ≤ s then jump v else 0) +
              (if s < v ∧ v ≤ t then jump v else 0)) := by
              apply tsum_congr
              intro v
              exact hpoint v
      _ = _ := ENNReal.tsum_add
  have hmass_real :
      (mass 0 t).toReal = (mass 0 s).toReal + (mass s t).toReal := by
    calc
      (mass 0 t).toReal = (mass 0 s + mass s t).toReal :=
        congrArg ENNReal.toReal hmass_split
      _ = (mass 0 s).toReal + (mass s t).toReal :=
        ENNReal.toReal_add (hmass_finite 0 s (show (0 : ℝ≥0) ≤ s from zero_le))
          (hmass_finite s t hst)
  obtain ⟨r, hr, hbalance⟩ := hreal_interval s t hst
  change S s - (mass 0 s).toReal ≤ S t - (mass 0 t).toReal
  rw [hmass_real]
  linarith only [hr, hbalance]
