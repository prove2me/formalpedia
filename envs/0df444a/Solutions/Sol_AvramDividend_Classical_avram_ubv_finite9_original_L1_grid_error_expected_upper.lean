-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_original_L1_grid_error_expected_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:18:10.636836+00:00
-- url     : https://prove2.me/submissions/6e3e390f-aa50-4200-874d-6ee0e867335c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite9_original_approximate_mean_zero_budget_implies_expected_upper

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- An original-source finite-grid upper budget with integrable centred
increments and an L1-small remainder implies the capped expected upper bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0)
    (σ : ℕ → Ω → ℝ≥0) (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (F : ℕ → Ω → ℝ)
    (hFsource : ∀ k ω, F k ω =
      Real.exp (-(q * (σ k ω : ℝ))) *
        w (if σ k ω = 0 ∨
              (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal)
    (hFI : ∀ k, Integrable (F k) P)
    (hApprox : ∀ k, ∃ M Err : ℕ → Ω → ℝ,
      (∀ j, Integrable (M j) P ∧ (∫ ω, M j ω ∂P) = 0) ∧
      (∀ j, Integrable (Err j) P) ∧
      Tendsto (fun j => ∫ ω, ‖Err j ω‖ ∂P) atTop (nhds (0 : ℝ)) ∧
      (∀ j, ∀ᵐ ω ∂P,
        F k ω ≤ w x + M j ω + Err j ω)) :
    ∀ k, (∫ ω, F k ω ∂P) ≤ w x := by
  apply avram_ubv_finite9_original_approximate_mean_zero_budget_implies_expected_upper
    X x q hq C hfinite w hw_cont hw_neg D hD τ σ hσle F hFsource hFI
  intro k
  obtain ⟨M, Err, hM, hErrI, hErrNorm, hBound⟩ := hApprox k
  refine ⟨M, Err, hM, hErrI, ?_, hBound⟩
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hLower : (fun _ : ℕ => (0 : ℝ)) ≤
      (fun j => ‖∫ ω, Err j ω ∂P‖) := by
    intro j
    exact norm_nonneg _
  have hUpper : (fun j => ‖∫ ω, Err j ω ∂P‖) ≤
      (fun j => ∫ ω, ‖Err j ω‖ ∂P) := by
    intro j
    exact norm_integral_le_integral_norm (Err j)
  exact Filter.Tendsto.squeeze tendsto_const_nhds hErrNorm hLower hUpper
