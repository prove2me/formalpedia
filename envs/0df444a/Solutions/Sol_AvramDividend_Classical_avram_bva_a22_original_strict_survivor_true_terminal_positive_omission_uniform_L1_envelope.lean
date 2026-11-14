-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_strict_survivor_true_terminal_positive_omission_uniform_L1_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:56:37.083017+00:00
-- url     : https://prove2.me/submissions/beb9231e-388c-41ca-875e-231816f860fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_04_original_BV_uniform_strict_survival_terminal_ae_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (hw_nonneg : ∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (x + X.X t ω - rightLimit D t ω))
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (S : ℝ≥0∞) < ruinTime X x D ω then
        max (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ m : ℕ, ∀ᵐ ω ∂P, Err m ω ≤ K := by
  intro S Err
  obtain ⟨K, hK, hUpper⟩ :=
    avram_wave8_04_original_BV_uniform_strict_survival_terminal_ae_bound
      X hX hBV q hq w hw_cont x D hD S
  refine ⟨K, hK, ?_⟩
  intro m
  filter_upwards [hUpper S le_rfl] with ω hω
  by_cases hSurvive : (S : ℝ≥0∞) < ruinTime X x D ω
  · have hden : 0 < (m : ℝ) + 2 := by positivity
    have hstep : ((m + 1 : ℕ) : ℝ) ≤ (m : ℝ) + 2 := by
      push_cast
      linarith
    have hlast : u m (m + 1) ≤ S := by
      change (u m (m + 1) : ℝ) ≤ T
      rw [huniform m (m + 1)]
      apply (div_le_iff₀ hden).2
      exact mul_le_mul_of_nonneg_left hstep (le_of_lt hT)
    have hlastPositive : 0 < u m (m + 1) := by
      change 0 < (u m (m + 1) : ℝ)
      rw [huniform m (m + 1)]
      positivity
    have hlastENN : (u m (m + 1) : ℝ≥0∞) ≤ (S : ℝ≥0∞) := by
      exact_mod_cast hlast
    have hlastBefore :
        (u m (m + 1) : ℝ≥0∞) < ruinTime X x D ω :=
      lt_of_le_of_lt hlastENN hSurvive
    have hwlast : 0 ≤
        w (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) :=
      hw_nonneg ω (u m (m + 1)) hlastPositive hlastBefore
    have hlastReward : 0 ≤
        Real.exp (-(q * (u m (m + 1) : ℝ))) *
          w (x + X.X (u m (m + 1)) ω -
            rightLimit D (u m (m + 1)) ω) :=
      mul_nonneg (Real.exp_pos _).le hwlast
    have hTermMax :
        max 0 (Real.exp (-(q * T)) *
          w (x + X.X S ω - rightLimit D S ω)) ≤ K := by
      rw [if_pos hSurvive] at hω
      exact hω
    have hTerm : Real.exp (-(q * T)) *
        w (x + X.X S ω - rightLimit D S ω) ≤ K :=
      (le_max_right _ _).trans hTermMax
    dsimp [Err]
    rw [if_pos hSurvive]
    exact max_le (by linarith) hK
  · dsimp [Err]
    rw [if_neg hSurvive]
    exact hK
