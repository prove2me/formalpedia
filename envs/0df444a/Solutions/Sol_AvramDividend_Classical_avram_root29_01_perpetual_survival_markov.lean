-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_perpetual_survival_markov
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T09:20:57.271604+00:00
-- url     : https://prove2.me/submissions/6b6520f8-c809-44b3-9567-f5f011f349da

import Theorems.Thm_AvramDividend_Classical_avram_root29_01_finite_killed_markov_real
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_history_survival_dct
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_lower_survival_mass_tendsto_iInf
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal

/-- Draft until e9833a53 is Proved: the true perpetual Esscher-survival
mass obeys the exact original-P killed history Markov identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (θ : ℝ) (hθ : 0 ≤ θ) (x : ℝ) (s : ℝ≥0) :
    (⨅ t : ℝ≥0, ∫ ω,
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp
          (θ * X.X t ω - (t : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ω ∂P) =
    (∫ ω, ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp
        (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
          (⨅ u : ℝ≥0, ∫ ζ,
            ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ (x + X.X s ω) + X.X v ζ}).indicator
              (fun ζ => Real.exp
                (θ * X.X u ζ - (u : ℝ) *
                  laplaceExponent X.c X.σ X.ν θ)) ζ ∂P)) ω ∂P) := by
  let F : ℝ≥0 → ℝ → ℝ := fun u z =>
    ∫ ζ, ({ζ | ∀ v : ℝ≥0, v ≤ u → 0 ≤ z + X.X v ζ}).indicator
      (fun ζ => Real.exp
        (θ * X.X u ζ - (u : ℝ) * laplaceExponent X.c X.σ X.ν θ)) ζ ∂P
  let R : ℝ≥0 → ℝ := fun u =>
    ∫ ω, ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp
        (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
          F u (x + X.X s ω)) ω ∂P
  let L : ℝ :=
    ∫ ω, ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp
        (θ * X.X s ω - (s : ℝ) * laplaceExponent X.c X.σ X.ν θ) *
          (⨅ u, F u (x + X.X s ω))) ω ∂P
  have hShift : Tendsto (fun u : ℝ≥0 => s + u) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with u hu
    exact le_trans hu (le_add_of_nonneg_left (show 0 ≤ s from zero_le))
  have hLeft := (esscher_weighted_lower_survival_mass_tendsto_iInf
    X θ hθ x).comp hShift
  change Tendsto (fun u => F (s + u) x) atTop
    (nhds (⨅ t, F t x)) at hLeft
  have hFinite (u : ℝ≥0) : F (s + u) x = R u := by
    obtain ⟨τ, hCover, hTerminal⟩ :=
      chat04_explicit_shifted_killed_survival_schedule u
    exact avram_root29_01_finite_killed_markov_real
      X θ hθ x s u τ hCover hTerminal
  have hFun : (fun u : ℝ≥0 => F (s + u) x) = R := by
    funext u
    exact hFinite u
  rw [hFun] at hLeft
  have hRight := avram_root29_01_history_survival_dct X θ hθ x s
  change Tendsto R atTop (nhds L) at hRight
  change (⨅ t, F t x) = L
  exact tendsto_nhds_unique hLeft hRight
