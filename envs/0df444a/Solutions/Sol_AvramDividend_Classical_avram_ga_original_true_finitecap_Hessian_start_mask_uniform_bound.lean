-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_true_finitecap_Hessian_start_mask_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:33:20.869582+00:00
-- url     : https://prove2.me/submissions/edf11d01-8d4d-47d5-9365-d4f55d96bc2e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_ga_discounted_masked_compact_Hessian_uniform_upper
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (a b q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ)
    (hFloor : ∀ (ω : Ω) (t : ℝ≥0), 0 < t → t < ρ ω →
      a ≤ riskProcess X x D t ω)
    (hCont : ContinuousOn (fun y => iteratedDeriv 2 w y) (Icc a b))
    (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m i : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      s < ρ ω →
      |Real.exp (-(q * (s : ℝ))) *
        (if x + X.X s ω - rightLimit D s ω ≤ b then
          iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
        else 0)| ≤ K := by
  let s : ℕ → ℕ → ℝ≥0 := fun m i =>
    (i : ℝ≥0) * ((n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0))
  let Y : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    x + X.X (s m i) ω - rightLimit D (s m i) ω
  let mask : ℕ → ℕ → Ω → Prop := fun m i ω =>
    s m i < ρ ω
  have hLow : ∀ m i ω, mask m i ω → a ≤ Y m i ω := by
    intro m i ω hm
    exact avram_gledger20_original_strict_prefix_postpayment_floor
      X x D hD ω (ρ ω) a (hFloor ω) (s m i) hm
  exact avram_ga_discounted_masked_compact_Hessian_uniform_upper
    w a b q hq hCont Y s mask hLow
