-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_topcap_actual_zero_or_strict_cash_grid_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:51:52.163581+00:00
-- url     : https://prove2.me/submissions/a6032c13-9305-49d9-bcd2-960f7a4213d8

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_topcap_zero_or_strict_payment_residual_cash_epsilon
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_actual_ruinstopped_grid_dividend_residual_source_cancellation
import Theorems.Thm_AvramDividend_Classical_avram_gledger111_subclock_le_ruin_and_horizon
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
(q : ℝ) (hq : 0 < q) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0)) (hw_neg : ∀ y < 0, w y = 0) (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
(hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
(x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t → (t : ℝ≥0∞) < ruinTime X x D ω → 0 ≤ w (riskProcess X x D t ω)) (hjump : ∀ ω (t : ℝ≥0),
(t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) → rightLimit D t ω - D t ω ≤ w (riskProcess X x D t ω) - w (riskProcess X x D t ω - (rightLimit D t ω - D t ω))) (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
(hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ) (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
(fun ω => (σ k ω : WithTop ℝ≥0))) (hσle : ∀ k ω, σ k ω ≤ τ ω) (hFsource : ∀ k ω, F k ω = Real.exp (-(q * (σ k ω : ℝ))) * w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
else riskProcess X x D (σ k ω) ω) + (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) (hFI : ∀ k, Integrable (F k) P)
(hInfiniteActivity : X.ν (Iio (0 : ℝ)) = ⊤) (hCapCase : C = ⊤) :
    ∀ k : ℕ,
      let Cash : Ω → ℝ := fun ω : Ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
      let u : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
      let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
      let Source : ℕ → Ω → ℝ := fun n ω =>
        let v : ℕ → ℝ≥0 := fun i => min (u n i) (σ k ω)
        let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
        let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
        let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
        ∑ i ∈ Finset.range (m n), ((E (v (i + 1)) - E (v i)) * w (Y (v i)) + E (v (i + 1)) * (w (Z i) - w (Y (v i))))
      let Dividend : ℕ → Ω → ℝ := fun n ω =>
        let v : ℕ → ℝ≥0 := fun i => min (u n i) (σ k ω)
        let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
        let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
        let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
        let pre : Prop := σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω
        (w (x - rightLimit D 0 ω) - w x) +
        (∑ i ∈ Finset.range (m n), ((E (v (i + 1)) - E (v i)) * w (Y (v i)) + E (v (i + 1)) * (w (Z i) - w (Y (v i))) + E (v (i + 1)) * (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) + E (v (i + 1)) * (w (Y (v (i + 1))) - w (riskProcess X x D (v (i + 1)) ω)))) +
        (if pre then 0 else E (σ k ω) * (w (riskProcess X x D (σ k ω) ω) - w (Y (σ k ω)))) - Source n ω
      ∀ᵐ ω ∂P,
        (σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω) → ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in atTop, Dividend j ω + Cash ω ≤ ε := by
  intro k
  let Cash : Ω → ℝ := fun ω : Ω => (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ), ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal
  let u : ℕ → ℕ → ℝ≥0 := fun j i => (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
  let m : ℕ → ℕ := fun j => (n + 1) * (j + 1)
  let Source : ℕ → Ω → ℝ := fun n ω =>
    let v : ℕ → ℝ≥0 := fun i => min (u n i) (σ k ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    ∑ i ∈ Finset.range (m n), ((E (v (i + 1)) - E (v i)) * w (Y (v i)) + E (v (i + 1)) * (w (Z i) - w (Y (v i))))
  let Dividend : ℕ → Ω → ℝ := fun n ω =>
    let v : ℕ → ℝ≥0 := fun i => min (u n i) (σ k ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i => x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let pre : Prop := σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω
    (w (x - rightLimit D 0 ω) - w x) +
    (∑ i ∈ Finset.range (m n), ((E (v (i + 1)) - E (v i)) * w (Y (v i)) + E (v (i + 1)) * (w (Z i) - w (Y (v i))) + E (v (i + 1)) * (w (riskProcess X x D (v (i + 1)) ω) - w (Z i)) + E (v (i + 1)) * (w (Y (v (i + 1))) - w (riskProcess X x D (v (i + 1)) ω)))) +
    (if pre then 0 else E (σ k ω) * (w (riskProcess X x D (σ k ω) ω) - w (Y (σ k ω)))) - Source n ω
  change ∀ᵐ ω ∂P,
        (σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω) →
        ∀ ε : ℝ, 0 < ε →
        ∀ᶠ j in atTop, Dividend j ω + Cash ω ≤ ε
  apply Filter.Eventually.of_forall
  intro ω hClock ε hε
  have hBound : σ k ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal := by
    rw [← hτeq ω]
    exact hσle k ω
  have ht : σ k ω ≤ (n : ℝ≥0) :=
    (avram_gledger111_subclock_le_ruin_and_horizon
      (ruinTime X x D ω) n (σ k ω) hBound).1
  have hsmooth1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.of_le (by norm_num)
  have hCashBound :=
    avram_jump6_B_original_topcap_zero_or_strict_payment_residual_cash_epsilon
      X x C hC hCapCase q (le_of_lt hq) w hw_cont hsmooth1 hw_grad
      D hD hjump ω (σ k ω) hClock n ht ε hε
  have hCancel :=
    avram_wave6_06_actual_ruinstopped_grid_dividend_residual_source_cancellation
      X x q w D (σ k) u m Source Dividend
      (by intro j η; rfl) (by intro j η; rfl)
  filter_upwards [hCashBound] with j hj
  calc
    Dividend j ω + Cash ω = Cash ω + Dividend j ω := by ring
    _ ≤ ε := by
      rw [hCancel j ω]
      simpa [Cash, u, m, hClock, add_assoc] using hj
