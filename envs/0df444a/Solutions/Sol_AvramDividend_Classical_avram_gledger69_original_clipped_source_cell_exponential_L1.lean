-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger69_original_clipped_source_cell_exponential_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T01:31:09.356339+00:00
-- url     : https://prove2.me/submissions/33c90843-1a75-4a02-be31-a5c609d7e759

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger62_original_bounded_stop_postpayment_exponential_L1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original terminal reserve of every clipped Gaussian source cell has
    the necessary upward exponential moment, with no independent process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (θ : ℝ) (hθ : 0 ≤ θ)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (Δ H : ℝ≥0) (ρ : Ω → ℝ≥0)
    (hρbound : ∀ ω, ρ ω ≤ H)
    (hvreal : ∀ i : ℕ, Measurable (fun ω =>
      ((min ((i : ℝ≥0) * Δ) (ρ ω) : ℝ≥0) : ℝ)))
    (hvstop : ∀ i : ℕ, IsStoppingTime 𝓕.rightCont (fun ω =>
      ((min ((i : ℝ≥0) * Δ) (ρ ω) : ℝ≥0) : WithTop ℝ≥0)))
    (hd0 : ∀ i ω, 0 ≤ rightLimit D (min ((i : ℝ≥0) * Δ) (ρ ω)) ω)
    (hExpMeas : ∀ i : ℕ, AEStronglyMeasurable (fun ω =>
      Real.exp (θ * (x +
        X.X (min (((i + 1 : ℕ) : ℝ≥0) * Δ) (ρ ω)) ω -
        rightLimit D (min ((i : ℝ≥0) * Δ) (ρ ω)) ω))) P) :
    ∀ i : ℕ, Integrable (fun ω =>
      Real.exp (θ * (x +
        X.X (min (((i + 1 : ℕ) : ℝ≥0) * Δ) (ρ ω)) ω -
        rightLimit D (min ((i : ℝ≥0) * Δ) (ρ ω)) ω))) P := by
  intro i
  exact avram_gledger62_original_bounded_stop_postpayment_exponential_L1
    X θ hθ x
    (fun ω => rightLimit D (min ((i : ℝ≥0) * Δ) (ρ ω)) ω)
    (hd0 i)
    (fun ω => min (((i + 1 : ℕ) : ℝ≥0) * Δ) (ρ ω))
    (hvreal (i + 1)) (hvstop (i + 1)) H
    (fun ω => (min_le_right _ _).trans (hρbound ω))
    (hExpMeas i)
