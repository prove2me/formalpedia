-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_physical_finite_grid_centred_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:07:08.217192+00:00
-- url     : https://prove2.me/submissions/d3b0f421-fe01-400c-9600-cc5f867cf2d0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_physical_band_centred_count_L2
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_grid_zero_mean_from_proved_compensator

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Physical original compensated finite-grid jump sums are integrable and centred. -/
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
    (hMeas : ∀ i, Measurable (N i))
    (H : ℕ → Ω → ℝ)
    (hH : ∀ i, StronglyMeasurable[𝓕 (grid i)] (H i))
    (hHL2 : ∀ i, MemLp (H i) 2 P)
    (K : ℕ → Ω → ℝ≥0∞)
    (hKMeas : ∀ i, Measurable (K i))
    (hPhysicalPair : ∀ i ω,
      (N i ω).toReal * ((N i ω).toReal - 1) = 2 * (K i ω).toReal)
    (hPairMean : ∀ i,
      (∫⁻ ω, K i ω ∂P) = ENNReal.ofReal
        (((((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal) ^ 2 / 2))
    (n : ℕ) :
    Integrable (fun ω => ∑ i ∈ Finset.range n,
      H i ω * ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal)) P ∧
    (∫ ω, (∑ i ∈ Finset.range n,
      H i ω * ((N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal)) ∂P) = 0 := by
  have hCountL2 (i : ℕ) :
      MemLp (fun ω => (N i ω).toReal -
        (((grid (i + 1) - grid i : ℝ≥0) : ℝ≥0∞) *
          X.ν (B i)).toReal) 2 P :=
    avram_p4_g_isometry_original_physical_band_centred_count_L2
      X (grid i) (grid (i + 1)) (hGrid i)
      ε hε (B i) (hB i) (hBand i) (hν i)
      (N i) (hActual i) (K i) (hKMeas i)
      (hPhysicalPair i) (hPairMean i)
  exact avram_p4_g_isometry_original_grid_zero_mean_from_proved_compensator
    X grid hGrid ε hε B hB hBand hν N hActual hMeas
    H hH hHL2 hCountL2 n
