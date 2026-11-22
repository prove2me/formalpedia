-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_original_physical_grid_centered_Levy_HJB_rightcash_expected_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T20:54:04.295488+00:00
-- url     : https://prove2.me/submissions/201e6e09-73e0-4dbe-a7ec-cec2445e2213

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L1_zero
import Theorems.Thm_AvramDividend_Classical_avram_b239_original_ruinclipped_physical_generator_and_right_payment_cash_negative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Exact physical HJB/right-payment signed ledger combined with the centred
original predictable Lévy increments on a finite stopping grid. The result
leaves mesh convergence, nonlinear Taylor terms, and true terminal
ruin-contact handling to the subsequent Ito–Meyer source proof. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ η (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D η) →
      rightLimit D t η - D t η ≤
        w (riskProcess X x D t η) -
          w (riskProcess X x D t η -
            (rightLimit D t η - D t η)))
    (σ : Ω → ℝ≥0) (n m : ℕ)
    (active : Ω → ℕ → Bool)
    (hInterior : ∀ ω, ∀ i ∈ Finset.range m, active ω i = true →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      let z := riskProcess X x D (v i) ω
      0 < z ∧ ENNReal.ofReal z < C)
    (hTimes : ∀ ω, ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      v i ≤ v (i + 1))
    (R : Ω → Finset ℝ≥0)
    (hPre : ∀ ω, ∀ u ∈ R ω,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω)
    (B : Ω → ℝ)
    (hBsource : ∀ ω, B ω = ((∑ i ∈ Finset.range m,
          if active ω i then
            Real.exp (-(q * (min ((i : ℝ≥0) *
              ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (σ ω) : ℝ))) *
              ((min (((i + 1 : ℕ) : ℝ≥0) *
                ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (σ ω) : ℝ) -
               (min ((i : ℝ≥0) *
                ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (σ ω) : ℝ)) *
              (X.generator w (riskProcess X x D
                  (min ((i : ℝ≥0) *
                    ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (σ ω)) ω) -
                q * w (riskProcess X x D
                  (min ((i : ℝ≥0) *
                    ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) (σ ω)) ω))
          else 0) +
      (∑ u ∈ R ω, Real.exp (-(q * (u : ℝ))) *
        ((rightLimit D u ω - D u ω) -
        (w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω)))))))
    (hBI : Integrable B P)
    (grid : ℕ → ℝ≥0)
    (hgrid : ∀ i, grid i ≤ grid (i + 1))
    (H : ℕ → Ω → ℝ) (κ : Ω → ℕ)
    (hWPast : ∀ i, Measurable[𝓕 (grid i)]
      (fun ω => if i < κ ω then H i ω else 0))
    (hWI : ∀ i, Integrable
      (fun ω => if i < κ ω then H i ω else 0) P)
    (hXI : ∀ i,
      Integrable (X.X (grid (i + 1) - grid i)) P)
    (hCellI : ∀ i ∈ Finset.range m, Integrable
      (fun ω => (if i < κ ω then H i ω else 0) *
        (X.X (grid (i + 1)) ω - X.X (grid i) ω -
          (∫ η, X.X (grid (i + 1) - grid i) η ∂P))) P) :
    let M : Ω → ℝ := fun ω => ∑ i ∈ Finset.range m, (if i < κ ω then H i ω else 0) *
        (X.X (grid (i + 1)) ω - X.X (grid i) ω -
          (∫ η, X.X (grid (i + 1) - grid i) η ∂P))
    Integrable (fun ω => M ω + B ω) P ∧
      (∫ ω, M ω + B ω ∂P) ≤ 0 := by
  intro M
  have hMI : Integrable M P := by
    change Integrable (fun ω => ∑ i ∈ Finset.range m,
      (if i < κ ω then H i ω else 0) *
        (X.X (grid (i + 1)) ω - X.X (grid i) ω -
          (∫ η, X.X (grid (i + 1) - grid i) η ∂P))) P
    exact integrable_finset_sum (Finset.range m) hCellI
  have hMzero : (∫ ω, M ω ∂P) = 0 := by
    change (∫ ω, ∑ i ∈ Finset.range m,
      (if i < κ ω then H i ω else 0) *
        (X.X (grid (i + 1)) ω - X.X (grid i) ω -
          (∫ η, X.X (grid (i + 1) - grid i) η ∂P)) ∂P) = 0
    rw [integral_finset_sum (Finset.range m) hCellI]
    apply Finset.sum_eq_zero
    intro i hi
    exact avram_wave7_06_original_stopped_predictable_gridcell_centered_X_L1_zero
      X grid i (hgrid i) H κ (hWPast i) (hWI i) (hXI i)
  have hBnonpos : ∀ ω, B ω ≤ 0 := by
    intro ω
    have hPoint :=
      avram_b239_original_ruinclipped_physical_generator_and_right_payment_cash_negative
        X q hq w C hC hw_gen x D hjump
        σ n m ω (active ω) (hInterior ω) (hTimes ω)
        (R ω) (hPre ω)
    rw [hBsource ω]
    simpa only [NNReal.coe_min, NNReal.coe_mul, NNReal.coe_div,
      NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one] using hPoint
  refine ⟨hMI.add hBI, ?_⟩
  rw [integral_add hMI hBI, hMzero, zero_add]
  exact integral_nonpos_of_ae (Filter.Eventually.of_forall hBnonpos)

