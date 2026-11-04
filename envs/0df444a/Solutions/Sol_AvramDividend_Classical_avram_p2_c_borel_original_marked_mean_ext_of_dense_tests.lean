-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_marked_mean_ext_of_dense_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:11:35.090791+00:00
-- url     : https://prove2.me/submissions/125178b6-21f5-4e16-9149-b357c76e6ee8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_cutoff_dense_halfline_ext

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Dense threshold tests determine all expected original marked counts below a finite cutoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (hFiniteMean : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) < ⊤)
    (ρ : Measure ℝ) (hρfin : ρ (Iic (-ε)) ≠ ⊤)
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ a : ℝ, a ∈ D →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) = ρ (Iic a ∩ Iic (-ε)))
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iic (-ε))) ∂P) = ρ (B ∩ Iic (-ε)) := by
  obtain ⟨μ, hμtotal, hμ⟩ :=
    avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
      X s t hst ε hε hFiniteMean
  have hμcut : μ (Iic (-ε)) ≠ ⊤ := by
    have hμle : μ (Iic (-ε)) ≤ μ Set.univ :=
      measure_mono (Set.subset_univ _)
    exact ne_of_lt (lt_of_le_of_lt hμle hμtotal)
  have hEqualTests : ∀ a : ℝ, a ∈ D →
      μ (Iic a ∩ Iic (-ε)) = ρ (Iic a ∩ Iic (-ε)) := by
    intro a ha
    calc
      μ (Iic a ∩ Iic (-ε)) =
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ ((Iic a ∩ Iic (-ε)) ∩ Iic (-ε))) ∂P) :=
        hμ (Iic a ∩ Iic (-ε)) (measurableSet_Iic.inter measurableSet_Iic)
      _ = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (Iic a ∩ Iic (-ε))) ∂P) := by
        simp only [inter_assoc, inter_self]
      _ = ρ (Iic a ∩ Iic (-ε)) := hTests a ha
  have hExt : μ.restrict (Iic (-ε)) = ρ.restrict (Iic (-ε)) :=
    avram_p2_c_borel_cutoff_dense_halfline_ext
      μ ρ (-ε) hμcut hρfin D hDense hEqualTests
  have hμcount : μ (B ∩ Iic (-ε)) = (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iic (-ε))) ∂P) := by
    simpa only [inter_assoc, inter_self] using
      (hμ (B ∩ Iic (-ε)) (hB.inter measurableSet_Iic))
  calc
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iic (-ε))) ∂P) = μ (B ∩ Iic (-ε)) := hμcount.symm
    _ = ρ (B ∩ Iic (-ε)) := by
      have hEval := congrArg (fun m : Measure ℝ => m B) hExt
      simpa only [Measure.restrict_apply hB] using hEval
