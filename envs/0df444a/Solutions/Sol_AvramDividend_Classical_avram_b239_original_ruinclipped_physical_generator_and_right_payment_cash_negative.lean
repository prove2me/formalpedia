-- Prove2me | solution 1 for AvramDividend.Classical.avram_b239_original_ruinclipped_physical_generator_and_right_payment_cash_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:11:30.08807+00:00
-- url     : https://prove2.me/submissions/066c144f-ca8d-44a9-824c-ec83f571a736

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

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
    (σ : Ω → ℝ≥0) (n m : ℕ) (ω : Ω)
    (active : ℕ → Bool)
    (hInterior : ∀ i ∈ Finset.range m, active i = true →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      let z := riskProcess X x D (v i) ω
      0 < z ∧ ENNReal.ofReal z < C)
    (hTimes : ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      v i ≤ v (i + 1))
    (R : Finset ℝ≥0)
    (hPre : ∀ u ∈ R,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    (∑ i ∈ Finset.range m, if active i then
      Real.exp (-(q * (v i : ℝ))) *
        ((v (i + 1) : ℝ) - (v i : ℝ)) *
        (X.generator w (riskProcess X x D (v i) ω) -
          q * w (riskProcess X x D (v i) ω))
      else 0) +
    (∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
      ((rightLimit D u ω - D u ω) -
        (w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω))))) ≤ 0 := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
  change
    (∑ i ∈ Finset.range m, if active i then
      Real.exp (-(q * (v i : ℝ))) *
        ((v (i + 1) : ℝ) - (v i : ℝ)) *
        (X.generator w (riskProcess X x D (v i) ω) -
          q * w (riskProcess X x D (v i) ω))
      else 0) +
    (∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
      ((rightLimit D u ω - D u ω) -
        (w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω))))) ≤ 0
  exact avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign
    X q hq w C hC hw_gen x D hjump
    (Finset.range m) v (fun i => v (i + 1))
    (fun i => riskProcess X x D (v i) ω) active
    (by intro i hi; exact hTimes i hi)
    (by intro i hi h; exact hInterior i hi h)
    ω R hPre
