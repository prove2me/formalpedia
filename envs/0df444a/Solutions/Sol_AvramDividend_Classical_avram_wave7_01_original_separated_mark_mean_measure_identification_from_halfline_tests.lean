-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_separated_mark_mean_measure_identification_from_halfline_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:43:12.637249+00:00
-- url     : https://prove2.me/submissions/b7d1acb4-1b2e-4e89-8ab3-026b097c916e


import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- The exact original separated jump-mark expected count is fixed by
finite half-line tests and the true prescribed Levy measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ B : Set ℝ, MeasurableSet B →
      μ B =
        (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ (B ∩ Iic (-ε))) ∂P))
    (hTests : ∀ a : ℝ,
      μ (Iic a) = (T : ℝ≥0∞) * X.ν (Iic a ∩ Iic (-ε)))
    (B : Set ℝ) (hB : MeasurableSet B) (hBsep : B ⊆ Iic (-ε)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) =
    (T : ℝ≥0∞) * X.ν B := by
  classical
  let νT : Measure ℝ := (T : ℝ≥0∞) • (X.ν.restrict (Iic (-ε)))
  have hEq : μ = νT := by
    apply Measure.ext_of_Iic μ νT
    intro a
    calc
      μ (Iic a) = (T : ℝ≥0∞) * X.ν (Iic a ∩ Iic (-ε)) := hTests a
      _ = νT (Iic a) := by
        simp only [νT, Measure.smul_apply,
          Measure.restrict_apply measurableSet_Iic]
        rfl
  have hInter : B ∩ Iic (-ε) = B := Set.inter_eq_left.mpr hBsep
  calc
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc 0 T ×ˢ B) ∂P) = μ B := by
        simpa only [hInter] using (hμ B hB).symm
    _ = νT B := congrArg (fun m : Measure ℝ => m B) hEq
    _ = (T : ℝ≥0∞) * X.ν B := by
      simp only [νT, Measure.smul_apply,
        Measure.restrict_apply hB, hInter]
      rfl