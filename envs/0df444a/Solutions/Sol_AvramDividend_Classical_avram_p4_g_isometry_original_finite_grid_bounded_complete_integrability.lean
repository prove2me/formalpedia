-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_bounded_complete_integrability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:25:42.985906+00:00
-- url     : https://prove2.me/submissions/37dbcd6c-722b-4400-a546-ade0359a5a61

import Mathlib.Data.Nat.Factorial.SuperFactorial
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_bounded_predictable_coeffs
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_integrable_diagonals_of_L2_Linfty

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Full source-conditioned original finite-band isometry: bounded predictable coefficients discharge all L² side conditions. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
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
    (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω))
    (hCountL2 : ∀ i, MemLp (fun ω =>
      (N i ω).toReal - r i) 2 P)
    (hSecond : ∀ i, P[(fun ω => ((N i ω).toReal - r i) ^ 2)
      | 𝓕 (grid i)] =ᵐ[P] (fun _ => r i))
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by
  letI : MeasurableSpace Ω := mΩ
  have hDiag (i : ℕ) :=
    avram_p4_g_isometry_integrable_diagonals_of_L2_Linfty
      (fun ω => (N i ω).toReal - r i) (H i) (hCountL2 i) (hHInf i)
  have hSq (i : ℕ) : Integrable (fun ω => ((N i ω).toReal - r i) ^ 2) P :=
    (hDiag i).1
  have hHSq (i : ℕ) : Integrable (fun ω => (H i ω) ^ 2) P :=
    (hDiag i).2.1
  have hWSq (i : ℕ) : Integrable (fun ω =>
      (H i ω) ^ 2 * ((N i ω).toReal - r i) ^ 2) P :=
    (hDiag i).2.2
  exact avram_p4_g_isometry_original_finite_grid_bounded_predictable_coeffs
    X grid hGrid ε hε B hB hBand hν N hActual
    r hRate H D hD hH hHInf hPrefix hCountL2 hSecond
    hSq hHSq hWSq n
