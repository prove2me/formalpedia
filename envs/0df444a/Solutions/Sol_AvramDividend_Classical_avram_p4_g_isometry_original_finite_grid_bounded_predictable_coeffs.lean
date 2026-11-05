-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_g_isometry_original_finite_grid_bounded_predictable_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:46:46.309773+00:00
-- url     : https://prove2.me/submissions/6523c03a-24a6-48a8-8643-fb52eff69872

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_L2_product_of_predictable_Linfty
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_finite_prefix_memLp_of_cells
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_grid_of_cell_L2

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators
noncomputable section

/-- Genuine original intrinsic bounded predictable finite-band L² isometry. -/
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
    (hPrefix : ∀ i, StronglyMeasurable[𝓕 (grid i)]
      (fun ω => ∑ j ∈ Finset.range i, D j ω))
    (hCountL2 : ∀ i, MemLp (fun ω =>
      (N i ω).toReal - r i) 2 P)
    (hSecond : ∀ i, P[(fun ω => ((N i ω).toReal - r i) ^ 2)
      | 𝓕 (grid i)] =ᵐ[P] (fun _ => r i))
    (hSq : ∀ i, Integrable (fun ω =>
      ((N i ω).toReal - r i) ^ 2) P)
    (hHSq : ∀ i, Integrable (fun ω => (H i ω) ^ 2) P)
    (hWSq : ∀ i, Integrable (fun ω =>
      (H i ω) ^ 2 * ((N i ω).toReal - r i) ^ 2) P)
    (n : ℕ) :
    (∫ ω, (∑ i ∈ Finset.range n, D i ω) ^ 2 ∂P) =
      ∑ i ∈ Finset.range n, r i * ∫ ω, (H i ω) ^ 2 ∂P := by
  letI : MeasurableSpace Ω := mΩ
  have hCellL2 (i : ℕ) : MemLp (D i) 2 P := by
    have hProduct := avram_p4_g_isometry_L2_product_of_predictable_Linfty
      (fun ω => (N i ω).toReal - r i) (H i) (hCountL2 i) (hHInf i)
    convert hProduct using 1
    funext ω
    simp only [hD i ω]
    ring
  have hPairL2 (i : ℕ) : MemLp (fun ω =>
      (∑ j ∈ Finset.range i, D j ω) * H i ω) 2 P :=
    avram_p4_g_isometry_L2_product_of_predictable_Linfty
      (fun ω => ∑ j ∈ Finset.range i, D j ω)
      (H i)
      (avram_p4_g_isometry_finite_prefix_memLp_of_cells D hCellL2 i)
      (hHInf i)
  exact avram_p4_g_isometry_original_finite_grid_of_cell_L2
    X grid hGrid ε hε B hB hBand hν N hActual
    r hRate H D hD hH hPrefix hPairL2 hCountL2 hSecond
    hSq hHSq hWSq hCellL2 n
