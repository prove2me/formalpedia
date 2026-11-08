-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian13_actual_stopped_bracket_expectation_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T13:42:38.19482+00:00
-- url     : https://prove2.me/submissions/ae22bfa6-86db-4227-9518-4b3cb0bcd9f8

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_square_energy_integrableOn
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_square_bracket_le_deterministic
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_actual_masked_terminal_bracket_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_bounded_stopped_bracket_L1
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_capped_ruin_bracket_le_horizon

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Bounded original-filtration stopping clocks preserve Gaussian bracket
expectations under a.e. convergence and the exact continuous-bracket interface. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (μtime : Measure ℝ≥0) [SFinite μtime] (T : ℝ≥0)
    (hFinite : μtime (Ioc (0 : ℝ≥0) T) < ⊤)
    (τ : Ω → ℝ≥0) (τn : ℕ → Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτnstop : ∀ n, IsStoppingTime 𝓕.rightCont
      (fun ω => (τn n ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ T)
    (hτnbound : ∀ n ω, τn n ω ≤ T)
    (hτconv : ∀ᵐ ω ∂P, Tendsto (fun n => τn n ω) atTop (𝓝 (τ ω))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    (∀ ω, Continuous (fun r : ℝ≥0 =>
      ∫ z in Ioc (0 : ℝ≥0) r, (G (z, ω)) ^ 2 ∂μtime)) →
    Tendsto (fun n => ∫ ω, (∫ z in Ioc (0 : ℝ≥0) (τn n ω),
      (G (z, ω)) ^ 2 ∂μtime) ∂P) atTop
      (𝓝 (∫ ω, (∫ z in Ioc (0 : ℝ≥0) (τ ω),
        (G (z, ω)) ^ 2 ∂μtime) ∂P)) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
  let H : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc u v then deriv w (Y p) else 0
  let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
  change (∀ ω, Continuous (fun r : ℝ≥0 =>
    ∫ z in Ioc (0 : ℝ≥0) r, (G (z, ω)) ^ 2 ∂μtime)) →
    Tendsto (fun n => ∫ ω, (∫ z in Ioc (0 : ℝ≥0) (τn n ω),
      (G (z, ω)) ^ 2 ∂μtime) ∂P) atTop
      (𝓝 (∫ ω, (∫ z in Ioc (0 : ℝ≥0) (τ ω),
        (G (z, ω)) ^ 2 ∂μtime) ∂P))
  intro hCont
  have hEnergy : ∀ ω, IntegrableOn (fun z : ℝ≥0 =>
      (G (z, ω)) ^ 2) (Ioc (0 : ℝ≥0) T) μtime :=
    avram_ubv_gaussian10_actual_masked_square_energy_integrableOn
      X x D hD w a b u v hw hau huv hvb μ hμ μtime T hFinite
  have hPredictable : Measurable[𝓕.rightCont.predictable] G :=
    (avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
      X x D hD w a b u v hw hau huv hvb μ hμ).1
  have hTerminalI : Integrable (fun ω =>
      ∫ z in Ioc (0 : ℝ≥0) T, (G (z, ω)) ^ 2 ∂μtime) P :=
    avram_ubv_gaussian10_actual_masked_terminal_bracket_L1
      X x D hD w a b u v hw hau huv hvb μ hμ μtime T hFinite
  have hLI : Integrable (fun ω =>
      ∫ z in Ioc (0 : ℝ≥0) (τ ω), (G (z, ω)) ^ 2 ∂μtime) P :=
    avram_ubv_gaussian10_original_bounded_stopped_bracket_L1
      X G hPredictable μtime τ hτstop T hτbound hEnergy hCont hTerminalI
  have hNI (n : ℕ) : Integrable (fun ω =>
      ∫ z in Ioc (0 : ℝ≥0) (τn n ω), (G (z, ω)) ^ 2 ∂μtime) P :=
    avram_ubv_gaussian10_original_bounded_stopped_bracket_L1
      X G hPredictable μtime (τn n) (hτnstop n) T
      (hτnbound n) hEnergy hCont hTerminalI
  have hw1 : ContDiffOn ℝ 1 w (Ioo a b) := hw.of_le (by norm_num)
  obtain ⟨K, hK, hTerminalBound⟩ :=
    avram_ubv_gaussian10_actual_masked_square_bracket_le_deterministic
      X x D hD w a b u v hw1 hau huv hvb μtime T hFinite
  let B : ℝ≥0 → Ω → ℝ := fun r ω =>
    ∫ z in Ioc (0 : ℝ≥0) r, (G (z, ω)) ^ 2 ∂μtime
  let C : ℝ := K ^ 2 * (μtime.restrict (Ioc (0 : ℝ≥0) T)).real Set.univ
  have hDom (n : ℕ) (ω : Ω) : ‖B (τn n ω) ω‖ ≤ C := by
    have hLe := avram_ubv_gaussian10_original_capped_ruin_bracket_le_horizon
      X G μtime (τn n) T hEnergy ω
    rw [min_eq_left (hτnbound n ω)] at hLe
    have hNonneg : 0 ≤ B (τn n ω) ω :=
      integral_nonneg (fun z => sq_nonneg (G (z, ω)))
    rw [Real.norm_eq_abs, abs_of_nonneg hNonneg]
    exact hLe.trans (hTerminalBound ω)
  have hDI : Integrable (fun _ : Ω => C) P := integrable_const _
  have hConv : ∀ᵐ ω ∂P,
      Tendsto (fun n => B (τn n ω) ω) atTop (𝓝 (B (τ ω) ω)) := by
    filter_upwards [hτconv] with ω hω
    exact ((hCont ω).tendsto (τ ω)).comp hω
  exact tendsto_integral_of_dominated_convergence (fun _ : Ω => C)
    (fun n => (hNI n).aestronglyMeasurable) hDI
    (fun n => Filter.Eventually.of_forall (hDom n)) hConv
