-- Prove2me | solution 1 for AvramDividend.Classical.avram_gaussianB_positive_event_full_original_stopped_GH_mesh_all_clippings_uniform
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T19:01:23.140926+00:00
-- url     : https://prove2.me/submissions/6e328754-49df-403a-b240-e393dad40b08

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
import Theorems.Thm_AvramDividend_Classical_avram_gbB117_original_lowerhit_stopped_GH_mesh_equals_fixed_horizon_noise
import Theorems.Thm_AvramDividend_Classical_avram_gbB131_original_gaussian_joint_tube_reserve_stop_and_mesh_noise
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
theorem solution
    [IsProbabilityMeasure gaussianLimit] :
    ∃ (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace (ℝ≥0 → ℝ)))
      (X : SpectrallyNegativeLevy gaussianLimit 𝓕),
      X.c = 2 ∧ X.σ = 1 ∧ X.ν = 0 ∧
      X.Standing ∧ ¬ X.BoundedVariation ∧
      IsAdmissibleLe X (1 / 8 : ℝ) (ENNReal.ofReal (1 / 8 : ℝ))
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ∧
      ∃ E : Set (ℝ≥0 → ℝ),
        MeasurableSet E ∧ 0 < gaussianLimit E ∧
        ∀ ω ∈ E, ∀ m : ℕ, 15999 ≤ m →
        ∀ (a : ℝ) (w : ℝ → ℝ),
          let Δ : ℝ≥0 := (1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
          let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
          let ρ : (ℝ≥0 → ℝ) → ℝ≥0 := fun η =>
            sInf ((Icc (0 : ℝ≥0) (1 / 1000 : ℝ≥0) ∩
              (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
                (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t η)) ⁻¹'
                Ici (-(5 / 44 : ℝ))) ∪ {(1 / 1000 : ℝ≥0)})
          let Y : ℕ → ℝ := fun i =>
            (1 / 8 : ℝ) + X.X (s i) ω -
              rightLimit (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (s i) ω
          let Z : ℕ → ℝ := fun i =>
            X.X (s (i + 1)) ω - X.X (s i) ω -
              ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c
          |(Finset.range (m + 1)).sum (fun i =>
            (if s i < ρ ω then
              Real.exp (-(1 / 100 : ℝ) * (s i : ℝ)) *
                (if Y i ∈ Icc a (5 / 44 : ℝ) then deriv w (Y i) else 1)
             else 0) * Z i +
            (if s i < ρ ω then
              (1 / 2 : ℝ) * Real.exp (-(1 / 100 : ℝ) * (s i : ℝ)) *
                (if Y i ∈ Icc a (5 / 44 : ℝ) then
                  iteratedDeriv 2 w (Y i) else 0)
             else 0) *
                (Z i ^ 2 - (Δ : ℝ) * X.σ ^ 2))| ≤
          (1 / 4000 : ℝ) := by
  obtain ⟨𝓕, X, hc, hσ, hν, hStanding, hBV, hAdm, E, hE, hEp, hTube⟩ :=
    AvramDividend.Classical.avram_gaussianB_original_triplet_positive_measurable_long_mesh_event
  refine ⟨𝓕, X, hc, hσ, hν, hStanding, hBV, hAdm, E, hE, hEp, ?_⟩
  intro ω hω m hm a w
  have hX0 : X.X 0 ω = 0 := X.X_zero ω
  let B : ℝ≥0 → (ℝ≥0 → ℝ) → ℝ := fun u η => brownian u η - brownian 0 η
  have hSrc : ∀ u : ℝ≥0, u ≤ (17 / 16000 : ℝ≥0) →
      X.X u ω = B u ω + 2 * (u : ℝ) := by
    intro u hu
    exact (hTube ω hω u hu).1
  have hB : ∀ u : ℝ≥0, u ≤ (17 / 16000 : ℝ≥0) →
      |B u ω| ≤ (1 / 4000 : ℝ) := by
    intro u hu
    exact (hTube ω hω u hu).2.1
  have hSmall : (1 / 1000 : ℝ≥0) ≤ (17 / 16000 : ℝ≥0) := by
    norm_num [div_le_div_iff₀]
  have hDrift : ∀ u : ℝ≥0, u ≤ (1 / 1000 : ℝ≥0) →
      |X.X u ω| ≤ (1 / 400 : ℝ) := by
    intro u hu
    exact (hTube ω hω u (hu.trans hSmall)).2.2
  obtain ⟨_, hStop, hNoise⟩ :=
    AvramDividend.Classical.avram_gbB131_original_gaussian_joint_tube_reserve_stop_and_mesh_noise
      X ω B hSrc hc hX0 hB hDrift m hm
  let Δ : ℝ≥0 := (1 : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
  let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
  let Z : ℕ → ℝ := fun i =>
    X.X (s (i + 1)) ω - X.X (s i) ω -
      ((s (i + 1) : ℝ) - (s i : ℝ)) * X.c
  let v : ℕ → ℝ := fun _ => (Δ : ℝ) * X.σ ^ 2
  let ρ : (ℝ≥0 → ℝ) → ℝ≥0 := fun η =>
    sInf ((Icc (0 : ℝ≥0) (1 / 1000 : ℝ≥0) ∩
      (fun t : ℝ≥0 => -(riskProcess X (1 / 8 : ℝ)
        (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) t η)) ⁻¹'
        Ici (-(5 / 44 : ℝ))) ∪ {(1 / 1000 : ℝ≥0)})
  have hEq :=
    avram_gbB117_original_lowerhit_stopped_GH_mesh_equals_fixed_horizon_noise
      X (1 / 1000 : ℝ≥0) ω hDrift ρ (by rfl) m s Z v
      (1 / 100 : ℝ) a w
  have hNoise' :
      |∑ i ∈ Finset.range (m + 1),
        if s i < (1 / 1000 : ℝ≥0) then
          Real.exp (-(1 / 100 * (s i : ℝ))) * Z i else 0| ≤
        (1 / 4000 : ℝ) := by
    simpa only [s, Δ, Z, neg_mul] using hNoise
  have hLe := (congrArg abs hEq).le.trans hNoise'
  simpa only [ρ, Δ, s, Z, v, hStop, neg_mul] using hLe
