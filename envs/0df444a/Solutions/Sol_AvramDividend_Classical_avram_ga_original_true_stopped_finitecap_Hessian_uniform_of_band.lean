-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_true_stopped_finitecap_Hessian_uniform_of_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:56:41.477446+00:00
-- url     : https://prove2.me/submissions/8258751e-c7b8-4647-80cf-12d4226ec41f

import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_ga_discounted_masked_compact_Hessian_uniform_upper
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (a b q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hFloor : ∀ ω (t : ℝ≥0), 0 < t → t < ρ ω →
      a ≤ riskProcess X x D t ω)
    (hCont : ContinuousOn (fun y => iteratedDeriv 2 w y) (Icc a b))
    (n : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (ω : Ω) (i : ℕ),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      i < m → s < ρ ω → s + Δ ≤ ρ ω →
      |Real.exp (-(q * (s : ℝ))) *
        (if x + X.X s ω - rightLimit D s ω ≤ b
        then iteratedDeriv 2 w (x + X.X s ω - rightLimit D s ω)
        else 0)| ≤ K  := by
  classical
  let s : ℕ → ℕ → ℝ≥0 := fun m i =>
    (i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
  let Y : ℕ → ℕ → Ω → ℝ := fun m i ω =>
    x + X.X (s m i) ω - rightLimit D (s m i) ω
  let active : ℕ → ℕ → Ω → Prop := fun m i ω =>
    i < m ∧ s m i < ρ ω ∧
      s m i + (n : ℝ≥0) / ((m : ℝ≥0) + 1) ≤ ρ ω
  have hY : ∀ m i ω, active m i ω → a ≤ Y m i ω := by
    intro m i ω ha
    have hPost :=
      avram_gledger20_original_strict_prefix_postpayment_floor
        X x D hD ω (ρ ω) a (hFloor ω)
    exact hPost (s m i) ha.2.1
  obtain ⟨K, hK, hBound⟩ :=
    avram_ga_discounted_masked_compact_Hessian_uniform_upper
      w a b q hq hCont Y s active hY
  refine ⟨K, hK, ?_⟩
  intro m ω i
  dsimp
  intro hi hs hc
  simpa [Y, s, NNReal.coe_mul] using (hBound m i ω ⟨hi, hs, hc⟩)
