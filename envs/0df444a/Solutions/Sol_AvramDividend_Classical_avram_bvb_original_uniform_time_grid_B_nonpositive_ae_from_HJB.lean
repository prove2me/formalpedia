-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_original_uniform_time_grid_B_nonpositive_ae_from_HJB
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T11:27:19.440298+00:00
-- url     : https://prove2.me/submissions/fa4eae4e-dfc4-4ff9-a68d-6dbc275f0d92

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_actual_BV_masked_physical_B_nonpositive_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (T : ℝ) (hT : 0 < T) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i =>
      ⟨T * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
    let Z : ℕ → ℕ → Ω → ℝ := fun n i ω => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
    let clock : ℕ → ℕ → Ω → Prop := fun n i ω =>
      (u n i : ℝ≥0∞) < ruinTime X x D ω
    let R : ℝ≥0 → Ω → ℝ := fun t ω =>
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) v - X.X v ω
         else 0)
    let coeff : ℕ → ℕ → Ω → ℝ := fun n i ω =>
      if clock n i ω ∧ 0 < Z n i ω ∧ ENNReal.ofReal (Z n i ω) < C then
        Real.exp (-(q * (u n i : ℝ))) * deriv w (Z n i ω)
      else 0
    let G : ℕ → Ω → ℝ := fun n ω =>
      ∑ i ∈ Finset.range (n + 1),
        if clock n i ω ∧ 0 < Z n i ω ∧ ENNReal.ofReal (Z n i ω) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z n i ω) - q * w (Z n i ω)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0
    let B : ℕ → Ω → ℝ := fun n ω => G n ω +
      (∑ i ∈ Finset.range (n + 1),
        coeff n i ω * (R (u n i) ω - R (u n (i + 1)) ω))
    ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0 := by
  let u : ℕ → ℕ → ℝ≥0 := fun n i =>
    ⟨T * (i : ℝ) / ((n : ℝ) + 2), by positivity⟩
  have hu : ∀ n i, u n i ≤ u n (i + 1) := by
    intro n i
    change T * (i : ℝ) / ((n : ℝ) + 2) ≤
      T * ((i + 1 : ℕ) : ℝ) / ((n : ℝ) + 2)
    have hden : 0 < (n : ℝ) + 2 := by positivity
    have hle : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) :=
      (by exact_mod_cast Nat.le_succ i)
    have hnum : T * (i : ℝ) ≤ T * ((i + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hle hT.le
    exact (div_le_div_iff₀ hden hden).2 (by nlinarith)
  exact avram_bvb_obstruction_actual_BV_masked_physical_B_nonpositive_ae
    X hX hBV q w C hGen x D u hu
