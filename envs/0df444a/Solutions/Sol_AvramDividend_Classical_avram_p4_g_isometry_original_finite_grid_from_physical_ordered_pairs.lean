-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_from_physical_ordered_pairs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:15:50.93047+00:00
-- url     : https://prove2.me/submissions/c48f6976-0a68-4522-8957-321bd6d17ec4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_factorial_from_physical_pair_lintegral
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_factorial_future_auto_first_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Original finite-grid predictable L2 isometry from physical ordered-pair count intensity on the same Levy path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0) (hGrid : ∀ i, grid i ≤ grid (i + 1))
    (ε : ℝ) (hε : 0 < ε) (B : ℕ → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hBand : ∀ i, B i ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : ∀ i, X.ν (B i) < ⊤)
    (N : ℕ → Ω → ℝ≥0∞)
    (hActual : ∀ i, N i = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (grid i) (grid (i + 1)) ×ˢ B i))
    (r : ℕ → ℝ)
    (hRate : ∀ i, r i =
      (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal)
    (H D : ℕ → Ω → ℝ)
    (hD : ∀ i ω, D i ω = H i ω * ((N i ω).toReal - r i))
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHInf : ∀ i, MemLp (H i) ⊤ P)
    (hCountEndpoint : ∀ i, StronglyMeasurable[𝓕 (grid (i + 1))]
      (fun ω => (N i ω).toReal))
    (K : ℕ → Ω → ℝ≥0∞)
    (hKMeas : ∀ i, Measurable (K i))
    (hPhysicalPair : ∀ i ω,
      (N i ω).toReal * ((N i ω).toReal - 1) = 2 * (K i ω).toReal)
    (hPairMean : ∀ i,
      (∫⁻ ω, K i ω ∂P) = ENNReal.ofReal
        (((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal) ^ 2 / 2))
    (mFuture : ℕ → MeasurableSpace Ω)
    (hFuture : ∀ i, mFuture i ≤ mΩ)
    (hSqMeas : ∀ i, StronglyMeasurable[mFuture i]
      (fun ω => ((N i ω).toReal - r i) ^ 2))
    (hIndependent : ∀ i, Indep (mFuture i) (𝓕 (grid i)) P)
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hFactorial (i : ℕ) :
      Integrable (fun ω =>
        (N i ω).toReal * ((N i ω).toReal - 1)) P ∧
      (∫ ω, (N i ω).toReal * ((N i ω).toReal - 1) ∂P) =
        ((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal) ^ 2 :=
    avram_p4_g_isometry_original_factorial_from_physical_pair_lintegral
      X (grid i) (grid (i + 1)) (hGrid i)
      ε hε (B i) (hB i) (hBand i) (hν i)
      (N i) (hActual i) (K i) (hKMeas i)
      (hPhysicalPair i) (hPairMean i)
  have hFacInt (i : ℕ) : Integrable (fun ω =>
      (N i ω).toReal * ((N i ω).toReal - 1)) P :=
    (hFactorial i).1
  have hFacMean (i : ℕ) :
      (∫ ω, (N i ω).toReal * ((N i ω).toReal - 1) ∂P) =
        (r i) ^ 2 := by
    rw [hRate i]
    exact (hFactorial i).2
  exact avram_p4_g_isometry_original_finite_grid_factorial_future_auto_first_mean
    X grid hGrid ε hε B hB hBand hν N hActual
    r hRate H D hD hH hHInf hCountEndpoint
    hFacInt hFacMean mFuture hFuture hSqMeas hIndependent n
