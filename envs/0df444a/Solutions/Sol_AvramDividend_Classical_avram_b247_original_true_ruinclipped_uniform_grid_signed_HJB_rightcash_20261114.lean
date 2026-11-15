-- Prove2me | solution 1 for AvramDividend.Classical.avram_b247_original_true_ruinclipped_uniform_grid_signed_HJB_rightcash_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:40:11.041776+00:00
-- url     : https://prove2.me/submissions/df5dc59f-5dc4-436a-b777-7f596b56a357

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hgen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hjump : ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (n m : ℕ) (σ : Ω → ℝ≥0)
    (hσbound : ∀ ω, σ ω ≤ (n : ℝ≥0))
    (hσclip : ∀ ω, σ ω ≤
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (ω : Ω) (R : Finset ℝ≥0)
    (hPre : ∀ u ∈ R,
      u = 0 ∨ (u : ℝ≥0∞) < ruinTime X x D ω)
    (y : ℕ → ℝ) (active : ℕ → Bool) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    (∀ i ∈ Finset.range (m + 1), active i = true →
      0 < y i ∧ ENNReal.ofReal (y i) < C) →
    (∑ i ∈ Finset.range (m + 1), if active i then
      Real.exp (-(q * (v i : ℝ))) *
        ((v (i + 1) : ℝ) - (v i : ℝ)) *
        (X.generator w (y i) - q * w (y i))
      else 0) +
    (∑ u ∈ R, Real.exp (-(q * (u : ℝ))) *
      ((rightLimit D u ω - D u ω) -
        (w (riskProcess X x D u ω) -
          w (riskProcess X x D u ω -
            (rightLimit D u ω - D u ω))))) ≤ 0 := by
  intro Δ v hInterior
  have hTime (i : ℕ) (_hi : i ∈ Finset.range (m+1)) :
      v i ≤ v (i+1) :=
    (avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
      n m (σ ω) i).1
  have hSign :=
    avram_b24_original_finite_ruinclipped_discrete_HJB_and_right_dividend_cash_ledger_sign
      X q hq w C hC hgen x D hjump
      (Finset.range (m+1)) (fun i => v i) (fun i => v (i+1))
      y active hTime hInterior ω R hPre
  simpa only [v, Δ] using hSign
