-- Prove2me | solution 1 for AvramDividend.Classical.avram_a26_original_gaussian_levy_assembly_from_path_independence_exponent_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T00:27:09.312243+00:00
-- url     : https://prove2.me/submissions/874fac4b-def6-4d6a-9418-b8511f74c90c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_raw_adapted_stationary_map_to_identDistrib_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Assemble the exact original-source zero-jump Levy structure once its remaining physical path and exponent certificates hold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (G : ℝ≥0 → Ω → ℝ)
    (hAdapt : ∀ t, Measurable[𝓕 t] (G t))
    (hZero : ∀ ω, G 0 ω = 0)
    (hRight : ∀ ω t, ContinuousWithinAt (fun s => G s ω) (Ici t) t)
    (hLeft : ∀ ω t, 0 < t →
      ∃ l, Tendsto (fun s => G s ω) (𝓝[<] t) (𝓝 l))
    (hNoPos : ∀ ω t l, 0 < t →
      Tendsto (fun s => G s ω) (𝓝[<] t) (𝓝 l) → G t ω ≤ l)
    (hInd : ∀ s t, s ≤ t →
      Indep (MeasurableSpace.comap
        (fun ω => G t ω - G s ω) inferInstance) (𝓕 s) P)
    (hLaw : ∀ s T,
      Measure.map (fun ω => G (s + T) ω - G s ω) P =
      Measure.map (G T) P)
    (hLap : ∀ (t : ℝ≥0) (θ : ℝ), 0 ≤ θ →
      Integrable (fun ω => Real.exp (θ * G t ω)) P ∧
      (∫ ω, Real.exp (θ * G t ω) ∂P) =
        Real.exp ((t : ℝ) *
          laplaceExponent 0 X.σ (0 : Measure ℝ) θ)) :
    ∃ Y : SpectrallyNegativeLevy P 𝓕,
      Y.ν = 0 ∧ Y.σ = X.σ ∧ Y.c = 0 ∧ Y.X = G := by
  let Y : SpectrallyNegativeLevy P 𝓕 := {
    X := G
    c := 0
    σ := X.σ
    ν := 0
    isProbability := X.isProbability
    σ_nonneg := X.σ_nonneg
    ν_Ici := by simp
    ν_integrable := by simp
    X_zero := hZero
    rightCont := hRight
    leftLim := hLeft
    noPosJumps := hNoPos
    adapted := hAdapt
    indepIncrements := hInd
    stationaryIncrements :=
      avram_a25_raw_adapted_stationary_map_to_identDistrib_20261114
        G hAdapt hLaw
    laplace := hLap
  }
  exact ⟨Y, rfl, rfl, rfl, rfl⟩
