-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_two_cell_L2_additivity_from_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:00:04.357218+00:00
-- url     : https://prove2.me/submissions/bc18518e-8ae2-49eb-9122-89de6c49e93a

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Additivity of source two-cell L² energy given exact zero cross moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (hSqA : Integrable (fun ω => (X.X (s + u) ω - X.X s ω)^2) P)
    (hSqB : Integrable (fun ω => (X.X (s + u + v) ω - X.X (s + u) ω)^2) P)
    (hAB : Integrable (fun ω =>
      (X.X (s + u) ω - X.X s ω) *
      (X.X (s + u + v) ω - X.X (s + u) ω)) P)
    (hZero : (∫ ω, (X.X (s + u) ω - X.X s ω) *
      (X.X (s + u + v) ω - X.X (s + u) ω) ∂P) = 0) :
    (∫ ω, (X.X (s + u + v) ω - X.X s ω)^2 ∂P) =
      (∫ ω, (X.X (s + u) ω - X.X s ω)^2 ∂P) +
      (∫ ω, (X.X (s + u + v) ω - X.X (s + u) ω)^2 ∂P) := by
  have hSum : Integrable (fun ω =>
      (X.X (s + u) ω - X.X s ω)^2 +
      (X.X (s + u + v) ω - X.X (s + u) ω)^2) P :=
    hSqA.add hSqB
  have hTwice : Integrable (fun ω => (2 : ℝ) *
      ((X.X (s + u) ω - X.X s ω) *
       (X.X (s + u + v) ω - X.X (s + u) ω))) P :=
    hAB.const_mul 2
  calc
    (∫ ω, (X.X (s + u + v) ω - X.X s ω)^2 ∂P) =
        ∫ ω, ((X.X (s + u) ω - X.X s ω)^2 +
          (X.X (s + u + v) ω - X.X (s + u) ω)^2) +
          (2 : ℝ) * ((X.X (s + u) ω - X.X s ω) *
            (X.X (s + u + v) ω - X.X (s + u) ω)) ∂P := by
      congr 1
      funext ω
      ring
    _ = (∫ ω, (X.X (s + u) ω - X.X s ω)^2 +
             (X.X (s + u + v) ω - X.X (s + u) ω)^2 ∂P) +
          (∫ ω, (2 : ℝ) * ((X.X (s + u) ω - X.X s ω) *
             (X.X (s + u + v) ω - X.X (s + u) ω)) ∂P) := by
      exact integral_add hSum hTwice
    _ = (∫ ω, (X.X (s + u) ω - X.X s ω)^2 ∂P) +
          (∫ ω, (X.X (s + u + v) ω - X.X (s + u) ω)^2 ∂P) := by
      rw [integral_add hSqA hSqB, integral_const_mul, hZero]
      ring
