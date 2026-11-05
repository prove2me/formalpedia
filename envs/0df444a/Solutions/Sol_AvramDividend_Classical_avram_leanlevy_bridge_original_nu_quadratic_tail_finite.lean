-- Prove2me | solution 1 for AvramDividend.Classical.avram_leanlevy_bridge_original_nu_quadratic_tail_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:20:26.8352+00:00
-- url     : https://prove2.me/submissions/ef06664a-6381-48ff-89ae-a22d5fb3f23f

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    (∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
      ENNReal.ofReal (z ^ 2) ∂X.ν) ≠ ⊤ := by
  let C : Set ℝ := Ioc (-(1 / ((n : ℝ) + 1))) 0
  let g : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (z ^ 2)
  let bound : ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (min (1 : ℝ) (z ^ 2))
  have hle : C.indicator g ≤ bound := by
    intro z
    by_cases hz : z ∈ C
    · have hδpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hnnonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      have hδle : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 :=
        (div_le_iff₀ hδpos).2 (by nlinarith [hnnonneg])
      have hzlow : -1 ≤ z := by
        have h := hz.1
        dsimp [C] at hz
        linarith
      have hzhigh : z ≤ 0 := hz.2
      have hmul : 0 ≤ (z + 1) * (-z) :=
        mul_nonneg (by linarith) (by linarith)
      have hsq : z ^ 2 ≤ (1 : ℝ) := by nlinarith [hmul]
      dsimp [g, bound]
      rw [Set.indicator_of_mem hz, min_eq_right hsq]
    · dsimp [g, bound]
      simp [Set.indicator_of_notMem hz]
  have hInt : (∫⁻ z, C.indicator g z ∂X.ν) =
      ∫⁻ z in C, g z ∂X.ν :=
    lintegral_indicator (by simp [C] : MeasurableSet C) g
  have hFin : (∫⁻ z, bound z ∂X.ν) < ⊤ := X.ν_integrable
  change (∫⁻ z in C, g z ∂X.ν) ≠ ⊤
  rw [← hInt]
  exact ne_of_lt (lt_of_le_of_lt (lintegral_mono hle) hFin)
