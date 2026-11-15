-- Prove2me | solution 1 for AvramDividend.Classical.avram_a54_construct_zero_nu_levy_on_identical_raw_filtration_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T12:15:35.458203+00:00
-- url     : https://prove2.me/submissions/0b412b64-0e79-4e3f-be60-1ddd4e569f0b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (G : ℝ≥0 → Ω → ℝ) (σ : ℝ)
    (hP : IsProbabilityMeasure P) (hσ : 0 ≤ σ)
    (hZero : ∀ ω, G 0 ω = 0)
    (hRight : ∀ ω t, ContinuousWithinAt (fun u => G u ω) (Ici t) t)
    (hLeft : ∀ ω t, 0 < t →
      ∃ l, Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l))
    (hNoPositive : ∀ ω t l, 0 < t →
      Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l) →
      G t ω ≤ l)
    (hAdapt : Adapted 𝓕 G)
    (hIndep : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap
        (fun ω => G t ω - G s ω) inferInstance) (𝓕 s) P)
    (hStat : ∀ s t, s ≤ t →
      IdentDistrib (fun ω => G t ω - G s ω) (G (t - s)) P P)
    (hLap : ∀ (t : ℝ≥0) (θ : ℝ), 0 ≤ θ →
      Integrable (fun ω => Real.exp (θ * G t ω)) P ∧
      (∫ ω, Real.exp (θ * G t ω) ∂P) =
        Real.exp ((t : ℝ) * (σ ^ 2 * θ ^ 2 / 2))) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.X = G ∧ Y.c = 0 ∧ Y.ν = 0 ∧ Y.σ = σ := by
  let Y : SpectrallyNegativeLevy P 𝓕 :=
    { X := G
      c := 0
      σ := σ
      ν := 0
      isProbability := hP
      σ_nonneg := hσ
      ν_Ici := by simp
      ν_integrable := by simp
      X_zero := hZero
      rightCont := hRight
      leftLim := hLeft
      noPosJumps := hNoPositive
      adapted := hAdapt
      indepIncrements := hIndep
      stationaryIncrements := hStat
      laplace := by
        intro t θ hθ
        obtain ⟨hInt, hExp⟩ := hLap t θ hθ
        refine ⟨hInt, ?_⟩
        simpa [laplaceExponent] using hExp }
  exact ⟨Y, rfl, rfl, rfl, rfl⟩
