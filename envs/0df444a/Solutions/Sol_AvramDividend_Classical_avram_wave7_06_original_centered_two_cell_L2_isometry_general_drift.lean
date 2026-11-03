-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_centered_two_cell_L2_isometry_general_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:56:03.0151+00:00
-- url     : https://prove2.me/submissions/0108ac13-9854-4ac3-95a2-4ec6c428748e

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_consecutive_centered_increment_covariance_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact two-cell source L² isometry for arbitrarily drifted increments after centring. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (hFirst : Integrable (fun ω => X.X (s + u) ω - X.X s ω) P)
    (hSecond : Integrable (fun ω =>
      X.X (s + u + v) ω - X.X (s + u) ω) P)
    (hSqA : Integrable (fun ω =>
      ((X.X (s + u) ω - X.X s ω) -
        (∫ η, X.X (s + u) η - X.X s η ∂P))^2) P)
    (hSqB : Integrable (fun ω =>
      ((X.X (s + u + v) ω - X.X (s + u) ω) -
        (∫ η, X.X (s + u + v) η - X.X (s + u) η ∂P))^2) P)
    (hAB : Integrable (fun ω =>
      ((X.X (s + u) ω - X.X s ω) -
        (∫ η, X.X (s + u) η - X.X s η ∂P)) *
      ((X.X (s + u + v) ω - X.X (s + u) ω) -
        (∫ η, X.X (s + u + v) η - X.X (s + u) η ∂P))) P) :
    (∫ ω,
      (((X.X (s + u) ω - X.X s ω) -
          (∫ η, X.X (s + u) η - X.X s η ∂P)) +
       ((X.X (s + u + v) ω - X.X (s + u) ω) -
          (∫ η, X.X (s + u + v) η - X.X (s + u) η ∂P)))^2 ∂P) =
      (∫ ω, ((X.X (s + u) ω - X.X s ω) -
        (∫ η, X.X (s + u) η - X.X s η ∂P))^2 ∂P) +
      (∫ ω, ((X.X (s + u + v) ω - X.X (s + u) ω) -
        (∫ η, X.X (s + u + v) η - X.X (s + u) η ∂P))^2 ∂P) := by
  let A : Ω → ℝ := fun ω =>
    (X.X (s + u) ω - X.X s ω) -
      (∫ η, X.X (s + u) η - X.X s η ∂P)
  let B : Ω → ℝ := fun ω =>
    (X.X (s + u + v) ω - X.X (s + u) ω) -
      (∫ η, X.X (s + u + v) η - X.X (s + u) η ∂P)
  have hA : Integrable (fun ω => (A ω)^2) P := hSqA
  have hB : Integrable (fun ω => (B ω)^2) P := hSqB
  have hProd : Integrable (fun ω => A ω * B ω) P := hAB
  have hZero : (∫ ω, A ω * B ω ∂P) = 0 :=
    avram_wave7_06_original_consecutive_centered_increment_covariance_zero
      X s u v hFirst hSecond
  have hSum : Integrable (fun ω => (A ω)^2 + (B ω)^2) P :=
    hA.add hB
  have hTwice : Integrable (fun ω => (2 : ℝ) * (A ω * B ω)) P :=
    hProd.const_mul 2
  change (∫ ω, (A ω + B ω)^2 ∂P) =
    (∫ ω, (A ω)^2 ∂P) + (∫ ω, (B ω)^2 ∂P)
  calc
    (∫ ω, (A ω + B ω)^2 ∂P) =
        ∫ ω, ((A ω)^2 + (B ω)^2) +
          (2 : ℝ) * (A ω * B ω) ∂P := by
      congr 1
      funext ω
      ring
    _ = (∫ ω, (A ω)^2 + (B ω)^2 ∂P) +
        (∫ ω, (2 : ℝ) * (A ω * B ω) ∂P) := by
      exact integral_add hSum hTwice
    _ = (∫ ω, (A ω)^2 ∂P) +
        (∫ ω, (B ω)^2 ∂P) := by
      rw [integral_add hA hB, integral_const_mul, hZero]
      ring
