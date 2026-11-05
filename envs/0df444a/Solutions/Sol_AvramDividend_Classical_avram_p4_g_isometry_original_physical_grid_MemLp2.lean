-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_physical_grid_MemLp2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:22:05.768135+00:00
-- url     : https://prove2.me/submissions/0ad848b2-bc00-4533-b9c5-7ae49fcc180d

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_physical_band_centred_count_L2
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_integrable_diagonals_of_L2_Linfty
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_finite_prefix_memLp_of_cells

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Physical original compensated predictable sums are actually square-integrable. -/
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
    (n : ℕ) :
    MemLp (fun ω => ∑ i ∈ Finset.range n, D i ω) 2 P := by
  have hCell (i : ℕ) : MemLp (D i) 2 P := by
    have hN2 :
        MemLp (fun ω => (N i ω).toReal - r i) 2 P := by
      simpa only [hRate i] using
        (avram_p4_g_isometry_original_physical_band_centred_count_L2
          X (grid i) (grid (i + 1)) (hGrid i)
          ε hε (B i) (hB i) (hBand i) (hν i)
          (N i) (hActual i) (K i) (hKMeas i)
          (hPhysicalPair i) (hPairMean i))
    have hProd : MemLp (fun ω =>
        H i ω * ((N i ω).toReal - r i)) 2 P := by
      simpa only using hN2.mul' (hHInf i)
    have hMeasH : StronglyMeasurable (H i) :=
      (hH i).mono (𝓕.le (grid i))
    have hMeasN : StronglyMeasurable
        (fun ω => (N i ω).toReal) :=
      (hCountEndpoint i).mono (𝓕.le (grid (i + 1)))
    have hMeasD : StronglyMeasurable (D i) := by
      have hFun : D i = fun ω => H i ω * ((N i ω).toReal - r i) := by
        funext ω
        exact hD i ω
      rw [hFun]
      exact hMeasH.mul (hMeasN.sub stronglyMeasurable_const)
    have hDSq : Integrable (fun ω => (D i ω) ^ 2) P := by
      have hProdSq : Integrable (fun ω =>
          (H i ω * ((N i ω).toReal - r i)) ^ 2) P :=
        (memLp_two_iff_integrable_sq hProd.1).1 hProd
      convert hProdSq using 1
      funext ω
      rw [hD i ω]
    exact (memLp_two_iff_integrable_sq hMeasD.aestronglyMeasurable).2 hDSq
  exact avram_p4_g_isometry_finite_prefix_memLp_of_cells D hCell n
