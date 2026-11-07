-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_source_cutoff_laplace_past_future_factor
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T18:06:58.088997+00:00
-- url     : https://prove2.me/submissions/08c0ec56-5f01-473d-a9ce-cc2424fd99e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_source_cutoff_measurable_path_version
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_source_cutoff_past_laplace_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable
import Theorems.Thm_AvramDividend_Classical_levy_deterministicTime_history_future_product_law
import Theorems.Thm_AvramDividend_Classical_levy_shiftedFuturePath_stationary_law
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
/-- Full Lévy path product law yields source original intrinsic past/future cutoff-Laplace independence. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (n k : ℕ),
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) * Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) =
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) *
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) := by
  intro n k
  letI : IsProbabilityMeasure P := X.isProbability
  let path0 : Ω → (ℝ≥0 → ℝ) := fun ω => fun t => X.X t ω
  let pathN : Ω → (ℝ≥0 → ℝ) := fun ω => fun t =>
    X.X ((n : ℝ≥0) + t) ω - X.X (n : ℝ≥0) ω
  let H : Ω → ℝ := fun ω => Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (n : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal))
  let V : Ω → ℝ := fun ω => Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if (n : ℝ≥0) < p.1 ∧ p.1 ≤ ((n + 1) : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal))
  change (∫ ω, H ω * V ω ∂P) = (∫ ω, H ω ∂P) * (∫ ω, V ω ∂P)
  rcases avram_bv_jump8_source_cutoff_measurable_path_version X hX hBV n k with
    ⟨F, hF, hBounds, hOriginal, hFuture⟩
  have hPast : Measurable[𝓕 (n : ℝ≥0)] H := by
    exact avram_bv_jump8_source_cutoff_past_laplace_filtration_measurable X hX hBV n k
  have hHM : Measurable H := hPast.mono (𝓕.le (n : ℝ≥0)) le_rfl
  have hN : Measurable pathN :=
    avram_wave7_01_original_shifted_future_path_coordinate_product_measurable X (n : ℝ≥0)
  have hLaw : Measure.map pathN P = Measure.map path0 P := by
    exact levy_shiftedFuturePath_stationary_law X (n : ℝ≥0)
  have hProduct :
      Measure.map (fun ω => (H ω, pathN ω)) P =
        (Measure.map H P).prod (Measure.map pathN P) := by
    calc
      Measure.map (fun ω => (H ω, pathN ω)) P =
          (Measure.map H P).prod (Measure.map path0 P) :=
        levy_deterministicTime_history_future_product_law X (n : ℝ≥0) H hPast
      _ = (Measure.map H P).prod (Measure.map pathN P) := by rw [← hLaw]
  have hInd : IndepFun H pathN P :=
    (indepFun_iff_map_prod_eq_prod_map_map hHM.aemeasurable hN.aemeasurable).2 hProduct
  have hIndF : IndepFun H (F ∘ pathN) P :=
    hInd.comp measurable_id hF
  have hFactor :
      (∫ ω, H ω * F (pathN ω) ∂P) =
        (∫ ω, H ω ∂P) * (∫ ω, F (pathN ω) ∂P) := by
    exact IndepFun.integral_fun_mul_eq_mul_integral
      hIndF hHM.aestronglyMeasurable (hF.comp hN).aestronglyMeasurable
  calc
    (∫ ω, H ω * V ω ∂P) = (∫ ω, H ω * F (pathN ω) ∂P) := by
      apply integral_congr_ae
      filter_upwards [hFuture] with ω hω
      exact congrArg (fun z : ℝ => H ω * z) hω.symm
    _ = (∫ ω, H ω ∂P) * (∫ ω, F (pathN ω) ∂P) := hFactor
    _ = (∫ ω, H ω ∂P) * (∫ ω, V ω ∂P) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hFuture] with ω hω
      exact hω
