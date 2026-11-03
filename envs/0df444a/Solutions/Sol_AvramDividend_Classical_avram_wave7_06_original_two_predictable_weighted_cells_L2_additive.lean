-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_two_predictable_weighted_cells_L2_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T18:28:26.010409+00:00
-- url     : https://prove2.me/submissions/841c14f9-0182-4570-abb2-a0fa0b2d88f5

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_consecutive_predictable_weighted_cells_cross_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

/-- Two consecutive predictable weighted original-source centred cells have
additive L² energy, provided all terms of the square expansion are integrable. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s u v : ℝ≥0)
    (W₀ W₁ : Ω → ℝ)
    (hW₀ : Measurable[𝓕 s] W₀)
    (hW₁ : Measurable[𝓕 (s + u)] W₁)
    (hXI : Integrable (X.X v) P)
    (hEarlierProduct : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) * W₁ ω) P)
    (hSqA : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P)))^2) P)
    (hSqB : Integrable (fun ω =>
      (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P)))^2) P)
    (hCross : Integrable (fun ω =>
      (W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) *
      (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P)))) P) :
    (∫ ω, ((W₀ ω * (X.X (s + u) ω - X.X s ω -
        (∫ η, X.X u η ∂P))) +
      (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
        (∫ η, X.X v η ∂P))))^2 ∂P) =
    (∫ ω, (W₀ ω * (X.X (s + u) ω - X.X s ω -
      (∫ η, X.X u η ∂P)))^2 ∂P) +
    (∫ ω, (W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω -
      (∫ η, X.X v η ∂P)))^2 ∂P) := by
  let A : Ω → ℝ := fun ω =>
    W₀ ω * (X.X (s + u) ω - X.X s ω - (∫ η, X.X u η ∂P))
  let B : Ω → ℝ := fun ω =>
    W₁ ω * (X.X (s + u + v) ω - X.X (s + u) ω - (∫ η, X.X v η ∂P))
  have hA : Integrable (fun ω => (A ω)^2) P := hSqA
  have hB : Integrable (fun ω => (B ω)^2) P := hSqB
  have hAB : Integrable (fun ω => A ω * B ω) P := hCross
  have hSourceZero :=
    avram_wave7_06_original_consecutive_predictable_weighted_cells_cross_zero
      X s u v W₀ W₁ hW₀ hW₁ hXI hEarlierProduct
  have hZero : (∫ ω, A ω * B ω ∂P) = 0 := by
    convert hSourceZero using 1
    congr 1
    funext ω
    dsimp [A, B]
    ring
  have hSum : Integrable (fun ω => (A ω)^2 + (B ω)^2) P := hA.add hB
  have hTwice : Integrable (fun ω => (2 : ℝ) * (A ω * B ω)) P :=
    hAB.const_mul 2
  change (∫ ω, (A ω + B ω)^2 ∂P) =
    (∫ ω, (A ω)^2 ∂P) + (∫ ω, (B ω)^2 ∂P)
  calc
    (∫ ω, (A ω + B ω)^2 ∂P) =
        ∫ ω, ((A ω)^2 + (B ω)^2) + (2 : ℝ) * (A ω * B ω) ∂P := by
      congr 1
      funext ω
      ring
    _ = (∫ ω, (A ω)^2 + (B ω)^2 ∂P) +
        (∫ ω, (2 : ℝ) * (A ω * B ω) ∂P) := by
      exact integral_add hSum hTwice
    _ = (∫ ω, (A ω)^2 ∂P) + (∫ ω, (B ω)^2 ∂P) := by
      rw [integral_add hA hB, integral_const_mul, hZero]
      ring
