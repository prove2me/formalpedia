-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_weighted_diagonal_of_factorial_independent_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:42:21.518272+00:00
-- url     : https://prove2.me/submissions/d2bfb1fa-9834-4f76-b331-6340f8bed7eb

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_conditional_finite_band_variance_of_independent_future
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped ENNReal NNReal
noncomputable section

/-- Physical predictable diagonal L² isometry from original factorial rate and independent future. -/
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
    (hJ : Integrable (fun ω => (N ω).toReal) P)
    (hFactorialIntegrable : Integrable (fun ω =>
      (N ω).toReal * ((N ω).toReal - 1)) P)
    (hFirst : (∫ ω, (N ω).toReal ∂P) = r)
    (hFactorial : (∫ ω,
      (N ω).toReal * ((N ω).toReal - 1) ∂P) = r ^ 2)
    (mFuture : MeasurableSpace Ω) (hFuture : mFuture ≤ mΩ)
    (hSqMeas : StronglyMeasurable[mFuture]
      (fun ω => ((N ω).toReal - r) ^ 2))
    (hFutureIndependent : Indep mFuture (𝓕 s) P)
    (H : Ω → ℝ) (hH : StronglyMeasurable[𝓕 s] H)
    (hSqInt : Integrable (fun ω => ((N ω).toReal - r) ^ 2) P)
    (hHSqInt : Integrable (fun ω => (H ω) ^ 2) P)
    (hWeightedSqInt : Integrable
      (fun ω => (H ω) ^ 2 * ((N ω).toReal - r) ^ 2) P) :
    (∫ ω, (H ω * ((N ω).toReal - r)) ^ 2 ∂P) =
      r * ∫ ω, (H ω) ^ 2 ∂P := by
  letI : MeasurableSpace Ω := mΩ
  have hSourceJ : ∀ ω, (N ω).toReal =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal := by
    intro ω
    rw [hActual]
  have hSecond :=
    avram_p4_b_smalljump_original_conditional_finite_band_variance_of_independent_future
      X s t B (fun ω => (N ω).toReal)
      hSourceJ hJ hFactorialIntegrable r hRate
      hFirst hFactorial mFuture hFuture hSqMeas hFutureIndependent
  exact avram_p4_g_isometry_original_raw_diagonal_of_source_second_rectangle
    X s t hst ε hε B hB hBand hν N hActual
    r hRate hSecond H hH hSqInt hHSqInt hWeightedSqInt
