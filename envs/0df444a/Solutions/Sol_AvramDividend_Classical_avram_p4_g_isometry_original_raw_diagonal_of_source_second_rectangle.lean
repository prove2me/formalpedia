-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:26:50.561583+00:00
-- url     : https://prove2.me/submissions/f4069852-6878-4a53-96d3-8b0610654ca4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

/-- Diagonal physical-band L² isometry from the exact original conditional second moment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B))
    (r : ℝ)
    (hRate : r = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)
    (hSecond : P[(fun ω => ((N ω).toReal - r) ^ 2) | 𝓕 s]
       =ᵐ[P] (fun _ => r))
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕 s] H)
    (hSqInt : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P)
    (hHSqInt : Integrable (fun ω => (H ω) ^ 2) P)
    (hWeightedSqInt : Integrable
      (fun ω => (H ω) ^ 2 * ((N ω).toReal - r) ^ 2) P) :
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) =
      r * ∫ ω, (H ω) ^ 2 ∂P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (m := 𝓕 s) (μ := P) (f := fun ω => (H ω) ^ 2)
    (g := fun ω => ((N ω).toReal - r) ^ 2)
    (hH.pow 2) hWeightedSqInt hSqInt
  have hcond : P[(fun ω => (H ω) ^ 2 * ((N ω).toReal - r) ^ 2) | 𝓕 s]
      =ᵐ[P] (fun ω => (H ω) ^ 2 * r) := by
    apply hpull.trans
    filter_upwards [hSecond] with ω hz
    simpa only [Pi.mul_apply, hz]
  calc
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) =
        ∫ ω, (H ω) ^ 2 * ((N ω).toReal - r) ^ 2 ∂P := by
          congr 1
          funext ω
          ring
    _ = ∫ ω, (P[(fun ω => (H ω) ^ 2 *
          ((N ω).toReal - r) ^ 2) | 𝓕 s]) ω ∂P := by
          symm
          exact integral_condExp (𝓕.le s)
    _ = ∫ ω, (H ω) ^ 2 * r ∂P := integral_congr_ae hcond
    _ = r * ∫ ω, (H ω) ^ 2 ∂P := by
          rw [integral_mul_const]
          ring
