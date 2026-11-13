-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_compact_masked_terminal_spatial_error_mean_vanish
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T00:44:14.20639+00:00
-- url     : https://prove2.me/submissions/c75ddc3b-6113-4f60-b67b-55e588a1f45d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_uniform_physical_discounted_terminal_strip_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (c d L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y ∈ Icc c d, ∀ z ∈ Icc c d,
      w z - w y ≤ L * max (z - y) 0)
    (T : ℝ) (hT : 0 < T) (u : ℕ → ℕ → ℝ≥0)
    (huniform : ∀ m i, (u m i : ℝ) =
      T * (i : ℝ) / ((m : ℝ) + 2)) :
    let S : ℝ≥0 := ⟨T, le_of_lt hT⟩
    let Err : ℕ → Ω → ℝ := fun m ω =>
      if (x + X.X (u m (m + 1)) ω -
            rightLimit D (u m (m + 1)) ω) ∈ Icc c d ∧
         (x + X.X S ω - rightLimit D S ω) ∈ Icc c d ∧
          0 ≤ w (x + X.X S ω - rightLimit D S ω) then
        max (Real.exp (-(q * T)) *
            w (x + X.X S ω - rightLimit D S ω) -
          Real.exp (-(q * (u m (m + 1) : ℝ))) *
            w (x + X.X (u m (m + 1)) ω -
              rightLimit D (u m (m + 1)) ω)) 0
      else 0
    (∀ m, Integrable (Err m) P) →
    Tendsto (fun m => ∫ ω, Err m ω ∂P) atTop (𝓝 (0 : ℝ)) := by
  intro S Err hErrI
  have hSource :=
    avram_bva_a22_original_uniform_physical_discounted_terminal_strip_bound
      X hBV x D hD w q hq c d L hL hLip T hT u huniform
  have hBound (m : ℕ) :
      ∀ᵐ ω ∂P, Err m ω ≤
        L * ((T / ((m : ℝ) + 2)) * max X.drift 0) := by
    filter_upwards [hSource] with ω hω
    by_cases h :
        (x + X.X (u m (m + 1)) ω -
          rightLimit D (u m (m + 1)) ω) ∈ Icc c d ∧
        (x + X.X S ω - rightLimit D S ω) ∈ Icc c d ∧
        0 ≤ w (x + X.X S ω - rightLimit D S ω)
    · dsimp [Err]
      rw [if_pos h]
      have hmain := hω m h.1 h.2.1 h.2.2
      have hden : 0 ≤ T / ((m : ℝ) + 2) :=
        div_nonneg (le_of_lt hT) (by positivity)
      exact max_le hmain
        (mul_nonneg hL (mul_nonneg hden (le_max_right _ _)))
    · dsimp [Err]
      rw [if_neg h]
      exact mul_nonneg hL (mul_nonneg
        (div_nonneg (le_of_lt hT) (by positivity)) (le_max_right _ _))
  have hEnd :=
    (avram_p3_grid4_original_uniform_strict_mesh_cofinal_at_horizon
      T hT).2
  have hDelta : Tendsto (fun m : ℕ => T / ((m : ℝ) + 2))
      atTop (𝓝 (0 : ℝ)) := by
    have hSub : Tendsto (fun m : ℕ =>
        T - (T - T / ((m : ℝ) + 2))) atTop (𝓝 (T - T)) :=
      tendsto_const_nhds.sub hEnd
    simpa using hSub
  have hUp : Tendsto (fun m : ℕ =>
      L * ((T / ((m : ℝ) + 2)) * max X.drift 0))
      atTop (𝓝 (0 : ℝ)) := by
    simpa using (hDelta.mul_const (max X.drift 0)).const_mul L
  apply squeeze_zero
  · intro m
    apply integral_nonneg
    intro ω
    dsimp [Err]
    split_ifs <;> positivity
  · intro m
    calc
      (∫ ω, Err m ω ∂P) ≤
        (∫ _ : Ω, L * ((T / ((m : ℝ) + 2)) * max X.drift 0) ∂P) :=
          integral_mono_ae (hErrI m) (integrable_const _) (hBound m)
      _ = L * ((T / ((m : ℝ) + 2)) * max X.drift 0) := by simp
  · exact hUp
