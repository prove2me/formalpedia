-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_original_canonical_openinterior_ruinclipped_grid_HJB_rightcash_sign
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T21:01:33.170669+00:00
-- url     : https://prove2.me/submissions/6e423b8b-6f55-4aa5-99c0-d16cb4dfc445

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b239_original_ruinclipped_physical_generator_and_right_payment_cash_negative
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

/-- The canonical physical clipped grid is monotone, and its Bool interior
indicator exactly enforces the generator's HJB open-domain hypotheses. -/
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
    (R : Finset ℝ≥0)
    (hPre : ∀ u ∈ R,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    let active : ℕ → Bool := fun i =>
      decide (0 < riskProcess X x D (v i) ω ∧
        ENNReal.ofReal (riskProcess X x D (v i) ω) < C)
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
  intro Δ v active
  have hInterior : ∀ i ∈ Finset.range m, active i = true →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      let z := riskProcess X x D (v i) ω
      0 < z ∧ ENNReal.ofReal z < C := by
    intro i hi ha
    change decide (0 < riskProcess X x D (v i) ω ∧
      ENNReal.ofReal (riskProcess X x D (v i) ω) < C) = true at ha
    exact of_decide_eq_true ha
  have hTimes : ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (σ ω)
      v i ≤ v (i + 1) := by
    intro i hi
    have hidx : (i : ℝ≥0) ≤ ((i + 1 : ℕ) : ℝ≥0) := by
      exact_mod_cast Nat.le_succ i
    exact min_le_min_right (σ ω)
      (mul_le_mul_of_nonneg_right hidx bot_le)
  exact avram_b239_original_ruinclipped_physical_generator_and_right_payment_cash_negative
    X q hq w C hC hw_gen x D hjump σ n m ω active hInterior hTimes R hPre

