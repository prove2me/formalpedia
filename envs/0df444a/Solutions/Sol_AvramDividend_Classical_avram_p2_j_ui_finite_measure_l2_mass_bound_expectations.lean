-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_j_ui_finite_measure_l2_mass_bound_expectations
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T22:11:38.640003+00:00
-- url     : https://prove2.me/submissions/15f96e47-92fd-4b86-b338-ca7f9fde6836

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_finite_measure_l2_l1_bound_expectations

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal

/-! On finite measures, L2 control and a finite mass bound imply Bochner mean convergence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (B R : ℝ≥0)
    (hm : ∀ n, AEStronglyMeasurable (Y n) μ)
    (hB : ∀ n, eLpNorm (Y n) 2 μ ≤ (B : ENNReal))
    (hMass : (μ Set.univ) ^ (1 / 2 : ℝ) ≤ (R : ENNReal))
    (hae : ∀ᵐ ω ∂μ, Tendsto (fun n => Y n ω) atTop (nhds (Z ω))) :
    Integrable Z μ ∧
      Tendsto (fun n => ∫ ω, Y n ω ∂μ) atTop
        (nhds (∫ ω, Z ω ∂μ)) := by
  have hL1 (n : ℕ) :
      eLpNorm (Y n) 1 μ ≤ ((B * R : ℝ≥0) : ENNReal) := by
    have h2 : MemLp (Y n) 2 μ :=
      ⟨hm n, lt_of_le_of_lt (hB n) (by simp)⟩
    have hcs :=
      eLpNorm_le_eLpNorm_mul_rpow_measure_univ
        (μ := μ) (p := 1) (q := 2) (by norm_num)
        h2.aestronglyMeasurable
    have hcs' : eLpNorm (Y n) 1 μ ≤
        eLpNorm (Y n) 2 μ * (μ Set.univ) ^ (1 / 2 : ℝ) := by
      convert hcs using 1 <;> norm_num
    calc
      eLpNorm (Y n) 1 μ ≤
          eLpNorm (Y n) 2 μ * (μ Set.univ) ^ (1 / 2 : ℝ) := hcs'
      _ ≤ (B : ENNReal) * (R : ENNReal) := by
          gcongr <;> first | exact hB n | exact hMass
      _ = ((B * R : ℝ≥0) : ENNReal) := by norm_cast
  exact avram_p2_j_ui_finite_measure_l2_l1_bound_expectations
    μ Y Z B (B * R) hm hB hL1 hae
