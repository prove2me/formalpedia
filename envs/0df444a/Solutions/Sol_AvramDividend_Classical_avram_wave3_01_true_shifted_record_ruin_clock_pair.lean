-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_true_shifted_record_ruin_clock_pair
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:41:56.35551+00:00
-- url     : https://prove2.me/submissions/58a6a4de-a7cd-4467-a953-a47500b61207

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_rightInterval_upper_strictExit_eq_schedule
import Theorems.Thm_AvramDividend_Classical_levy_shiftedUpper_strictCrossing_rightInterval
import Theorems.Thm_AvramDividend_Classical_avram_root29_05_shifted_strict_drawdown_clock_eq_cantor_schedule
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
import Theorems.Thm_AvramDividend_Classical_chat05_cantor_rational_schedule_dense

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped NNReal ENNReal

/-- The genuine shifted strict record and reflected-ruin clocks are exactly the
countable Borel future-path clocks used by the stopped strong-Markov reward. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (u : ℝ≥0) (a c : ℝ) :
    (let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let M : ℝ≥0 → ℝ := fun t => sSup (f '' Set.Icc 0 t)
     ((⨅ i : {t : ℝ≥0 // c < f t}, (i.1 : ℝ≥0∞)),
      (⨅ i : {t : ℝ≥0 // f t - M t < -a}, (i.1 : ℝ≥0∞)))) =
    (let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
     let samples : ℕ → ℝ≥0 := fun j =>
       ((Nat.unpair j).2 : ℝ≥0) *
         (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
     ((⨅ j : ℕ, if c < f (samples j)
          then (samples j : ℝ≥0∞) else ⊤),
      (⨅ j : ℕ, if f (samples j) -
        (⨆ k : ℕ, if samples k ≤ samples j
           then ENNReal.ofReal (f (samples k)) else 0).toReal < -a
          then (samples j : ℝ≥0∞) else ⊤))) := by
  let f : ℝ≥0 → ℝ := fun t => X.X (u + t) ω - X.X u ω
  let samples : ℕ → ℝ≥0 := fun j =>
    ((Nat.unpair j).2 : ℝ≥0) *
      (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)
  let M : ℝ≥0 → ℝ := fun t => sSup (f '' Set.Icc 0 t)
  have hdense : Dense (Set.range samples) := by
    exact chat05_cantor_rational_schedule_dense
  have hzero : (0 : ℝ≥0) ∈ Set.range samples := by
    refine ⟨Nat.pair 0 0, ?_⟩
    simp [samples]
  have hM (j : ℕ) :
      (⨆ k : ℕ, if samples k ≤ samples j
          then ENNReal.ofReal (f (samples k)) else 0).toReal =
      M (samples j) := by
    exact avram_ws01e_b_actual_shifted_levy_dense_prefix_eq_shiftedSup
      X ω u samples hdense hzero (samples j) ⟨j, rfl⟩
  have hρ :
      (⨅ i : {t : ℝ≥0 // c < f t}, (i.1 : ℝ≥0∞)) =
      (⨅ j : ℕ, if c < f (samples j)
        then (samples j : ℝ≥0∞) else ⊤) := by
    simpa [f, samples] using
      (rightInterval_upper_strictExit_eq_schedule f c
        (levy_shiftedUpper_strictCrossing_rightInterval X ω u c))
  have hσ :
      (⨅ i : {t : ℝ≥0 // f t - M t < -a}, (i.1 : ℝ≥0∞)) =
      (⨅ j : ℕ, if f (samples j) -
        (⨆ k : ℕ, if samples k ≤ samples j
           then ENNReal.ofReal (f (samples k)) else 0).toReal < -a
        then (samples j : ℝ≥0∞) else ⊤) := by
    calc
      _ = (⨅ j : ℕ, if f (samples j) - M (samples j) < -a
        then (samples j : ℝ≥0∞) else ⊤) := by
          simpa only [f, M, samples] using
            (avram_root29_05_shifted_strict_drawdown_clock_eq_cantor_schedule
              X ω u a)
      _ = _ := by
        apply iInf_congr
        intro j
        rw [hM j]
  exact Prod.ext hρ hσ
