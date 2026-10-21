-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_esscher_grid_upper_exit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-20T20:05:14.031965+00:00
-- url     : https://prove2.me/submissions/476a955b-1572-4765-9170-f03ef1227bf9

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_gaussian
import Theorems.Thm_AvramDividend_Classical_levy_grid_upper_exit_discount_bound_complete
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The Gaussian Esscher root supplies the q-discounted two-sided-grid upper-exit estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hσ : 0 < X.σ)
    (clock : ℕ → NNReal) (hc : Monotone clock) (hc0 : clock 0 = 0)
    (H : Filtration ℕ mΩ) (hH : ∀ k, H k = 𝓕 (clock k))
    (lower upper : ℝ) (m : ℕ)
    (K : Ω → ℕ)
    (hK : ∀ ω, K ω = hittingBtwn
      (fun k ω => max (X.X (clock k) ω - upper)
        (lower - X.X (clock k) ω)) (Ioi (0 : ℝ)) 0 m ω) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
      (∫ ω, {ω : Ω | upper < X.X (clock (K ω)) ω}.indicator
        (fun z => Real.exp (-((clock (K z)) : ℝ) * q)) ω ∂P) ≤
        Real.exp (-φ * upper) := by
  obtain ⟨φ, hφ, hψ⟩ :=
    positive_esscher_root_of_gaussian X q hq hσ
  refine ⟨φ, hφ, hψ, ?_⟩
  have hψ_nonneg : 0 ≤ X.ψ φ := by
    rw [hψ]
    exact le_of_lt hq
  have hbound :=
    levy_grid_upper_exit_discount_bound_complete
      X clock hc hc0 H hH φ (le_of_lt hφ) hψ_nonneg
      lower upper m K hK
  simpa only [hψ] using hbound
