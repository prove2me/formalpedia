-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_source_cutoff_laplace_future_stationary
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:59:23.278534+00:00
-- url     : https://prove2.me/submissions/8b9bcabe-e0a5-4ce2-9212-b01473149420
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_source_cutoff_measurable_path_version
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Exact original future marked-Laplace expectation stationarity from a measurable source path version. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ),
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) =
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) := by
  intro n k
  let path0 : Ω → (ℝ≥0 → ℝ) := fun ω => fun t => X.X t ω
  let pathN : Ω → (ℝ≥0 → ℝ) := fun ω => fun t =>
    X.X ((n : ℝ≥0) + t) ω - X.X (n : ℝ≥0) ω
  let A : Ω → ℝ := fun ω => Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (1 : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal))
  let B : Ω → ℝ := fun ω => Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal))
  change (∫ ω, B ω ∂P) = ∫ ω, A ω ∂P
  rcases avram_bv_jump8_source_cutoff_measurable_path_version X hX hBV n k with
    ⟨F, hF, hBounds, hOriginal, hFuture⟩
  have h0 : Measurable path0 := by
    convert (avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
      X (0 : ℝ≥0)) using 1
    funext ω t
    simp [path0, X.X_zero]
  have hN : Measurable pathN := by
    exact avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
      X (n : ℝ≥0)
  have hLaw : Measure.map pathN P = Measure.map path0 P := by
    exact levy_shiftedFuturePath_stationary_law X (n : ℝ≥0)
  have hTransfer :
      (∫ ω, F (pathN ω) ∂P) = ∫ ω, F (path0 ω) ∂P := by
    calc
      (∫ ω, F (pathN ω) ∂P) =
          ∫ f, F f ∂(Measure.map pathN P) :=
        (integral_map hN.aemeasurable hF.aestronglyMeasurable).symm
      _ = ∫ f, F f ∂(Measure.map path0 P) := by rw [hLaw]
      _ = ∫ ω, F (path0 ω) ∂P :=
        integral_map h0.aemeasurable hF.aestronglyMeasurable
  calc
    (∫ ω, B ω ∂P) = ∫ ω, F (pathN ω) ∂P := by
      apply integral_congr_ae
      filter_upwards [hFuture] with ω hω
      exact hω.symm
    _ = ∫ ω, F (path0 ω) ∂P := hTransfer
    _ = ∫ ω, A ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hOriginal] with ω hω
      exact hω
