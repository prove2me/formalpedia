-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva32_original_BV_finitecap_physical_HJB_R_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:47:28.827953+00:00
-- url     : https://prove2.me/submissions/03e549f4-086f-4066-a838-652b45320ed1

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva31_original_BV_physical_drift_jump_R_vanishes
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) :
    ∀ᵐ ω ∂P, ∀ n : ℕ,
      let Z : ℕ → ℝ := fun i =>
        Function.leftLim
          (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0
      let R : ℝ≥0 → ℝ := fun t =>
        ((t : ℝ) * X.drift - X.X t ω) - J t
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) +
      (∑ i ∈ Finset.range (n + 1),
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
        else 0) * (R (u n i) - R (u n (i + 1)))) ≤ 0 := by
  filter_upwards [avram_bva31_original_BV_physical_drift_jump_R_vanishes X hX hBV]
    with ω hR
  intro n
  let Z : ℕ → ℝ := fun i =>
    Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
  let J : ℝ≥0 → ℝ := fun t =>
    ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
      Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
    else 0
  let R : ℝ≥0 → ℝ := fun t => ((t : ℝ) * X.drift - X.X t ω) - J t
  have hR0 : ∀ t : ℝ≥0, R t = 0 := by
    intro t
    simpa only [R, J] using hR t
  have hSecond :
      (∑ i ∈ Finset.range (n + 1),
        (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
        else 0) * (R (u n i) - R (u n (i + 1)))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hR0 (u n i), hR0 (u n (i + 1))]
    ring
  have hFirst :
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    by_cases mask : (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z i ∧ ENNReal.ofReal (Z i) < C
    · rw [if_pos mask]
      have hg := (hw_gen (Z i) mask.2.1 mask.2.2).2
      have hstep : u n i ≤ u n (i + 1) :=
        hmono n i (Finset.mem_range.mp hi)
      have hΔ : 0 ≤ ((u n (i + 1) : ℝ) - (u n i : ℝ)) := by
        exact sub_nonneg.mpr (by exact_mod_cast hstep)
      exact mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (Real.exp_nonneg _) hg) hΔ
    · simp [mask]
  dsimp only
  rw [hSecond]
  simpa using hFirst
