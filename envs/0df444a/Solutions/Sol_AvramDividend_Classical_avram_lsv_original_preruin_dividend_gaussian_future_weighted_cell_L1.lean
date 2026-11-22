-- Prove2me | solution 1 for AvramDividend.Classical.avram_lsv_original_preruin_dividend_gaussian_future_weighted_cell_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:25:06.366804+00:00
-- url     : https://prove2.me/submissions/88b42f2e-a55c-4109-9ce6-4e2b4b5677a9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_rightcont_discounted_preruin_single_atom_L2
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_zerojump_fixed_cell_second_fourth_power_integrable
import Theorems.Thm_AvramDividend_Classical_avram_lsv_original_rightcont_stopped_gaussian_weighted_sqrt_time_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_ja20_integrable_product_of_square_integrable
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hBV : ¬ X.BoundedVariation) (hσ : 0 < X.σ)
    (x : ℝ) (hx : 0 ≤ x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (n s : ℝ≥0) (hsn : s ≤ n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω)
    (q : ℝ) (hq : 0 ≤ q)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    let H : Ω → ℝ := fun ω =>
      if s < ρ ω then
        Real.exp (-(q * (s : ℝ))) *
          (rightLimit D s ω - D s ω)
      else 0
    let Z : Ω → ℝ := fun ω =>
      X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
    Integrable (fun ω => H ω * |Z ω|) P ∧
      Integrable (fun ω => H ω * (Z ω)^2) P ∧
      (∫ ω, H ω * |Z ω| ∂P) ≤
        X.σ * Real.sqrt (Δ : ℝ) * (∫ ω, H ω ∂P) := by
  classical
  let H : Ω → ℝ := fun ω =>
    if s < ρ ω then
      Real.exp (-(q * (s : ℝ))) *
        (rightLimit D s ω - D s ω)
    else 0
  let Z : Ω → ℝ := fun ω =>
    X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c
  obtain ⟨hHm, hHI, hH2, hHnonneg⟩ :=
    avram_lsv_original_rightcont_discounted_preruin_single_atom_L2
      X hBV hσ x hx D hD n s hsn ρ hρstop hρruin q hq
  obtain ⟨hZ2, hZ4⟩ :=
    avram_lsv_original_zerojump_fixed_cell_second_fourth_power_integrable
      X hν hσ s Δ
  have hHg : Measurable H := hHm.mono (𝓕.rightCont.le s) le_rfl
  have hZm : Measurable Z := by
    dsimp [Z]
    exact (((X.adapted (s + Δ)).mono (𝓕.le _) le_rfl).sub
      ((X.adapted s).mono (𝓕.le _) le_rfl)).sub measurable_const
  have hProd1 : Integrable (fun ω => H ω * |Z ω|) P := by
    apply avram_ja20_integrable_product_of_square_integrable
      P H (fun ω => |Z ω|)
      hHg.aestronglyMeasurable (hZm.abs.aestronglyMeasurable) hH2
    simpa only [sq_abs] using hZ2
  have hProd2 : Integrable (fun ω => H ω * (Z ω)^2) P := by
    apply avram_ja20_integrable_product_of_square_integrable
      P H (fun ω => (Z ω)^2)
      hHg.aestronglyMeasurable ((hZm.pow_const 2).aestronglyMeasurable) hH2
    convert hZ4 using 1
    ext ω
    ring
  let τ : Ω → ℝ≥0 := fun _ => s
  have hEvents : ∀ t : ℝ≥0,
      MeasurableSet[𝓕.rightCont t] {ω : Ω | τ ω ≤ t} := by
    intro t
    by_cases hst : s ≤ t <;> simp [τ, hst]
  have hStop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) :=
    isStoppingTime_withTop_of_le_events τ hEvents
  have hHStop :
      Measurable[(isStoppingTime_withTop_of_le_events τ hEvents).measurableSpace] H := by
    have heq : (isStoppingTime_withTop_of_le_events τ hEvents).measurableSpace =
        𝓕.rightCont s := by
      simpa only [τ] using
        (IsStoppingTime.measurableSpace_const 𝓕.rightCont s)
    rw [heq]
    exact hHm
  have hBound : ∀ ω, τ ω ≤ s := by intro ω; exact le_rfl
  have hSource :=
    avram_lsv_original_rightcont_stopped_gaussian_weighted_sqrt_time_first_moment
      X hν τ hEvents hStop s hBound Δ H hHStop hHg
      hHnonneg hHI
      (by simpa only [Z, τ] using hProd1)
      (by simpa only [Z, τ] using hProd2) hσ hΔ
  exact ⟨hProd1, hProd2, by simpa only [Z, τ] using hSource⟩

