-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_actual_BV_masked_physical_B_nonpositive_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:17:26.253639+00:00
-- url     : https://prove2.me/submissions/33fce8c7-acc0-47be-af3b-e97740784fde

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb46_original_all_BV_residual_grid_B_equals_true_generator_G_ae
import Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_masked_physical_generator_grid_nonpositive
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
    (u : ℕ → ℕ → ℝ≥0)
    (hu : ∀ n i, u n i ≤ u n (i + 1)) :
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
  dsimp
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
  have hR : ∀ t ω, R t ω =
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) v - X.X v ω
         else 0) := by
    intro t ω
    rfl
  have hB : ∀ n ω, B n ω = G n ω +
      (∑ i ∈ Finset.range (n + 1),
        coeff n i ω * (R (u n i) ω - R (u n (i + 1)) ω)) := by
    intro n ω
    rfl
  have hEq := avram_bvb46_original_all_BV_residual_grid_B_equals_true_generator_G_ae
    X hX hBV u R hR coeff B G hB
  filter_upwards [hEq] with ω hω
  intro n
  change B n ω ≤ 0
  rw [hω n]
  change (∑ i ∈ Finset.range (n + 1),
      if clock n i ω ∧ 0 < Z n i ω ∧ ENNReal.ofReal (Z n i ω) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z n i ω) - q * w (Z n i ω)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0) ≤ 0
  apply Finset.sum_nonpos
  intro i hi
  split_ifs with hmask
  · rcases hmask with ⟨_, hpos, hcap⟩
    have hResidual := (hGen (Z n i ω) hpos hcap).2
    have hTime : 0 ≤ (u n (i + 1) : ℝ) - (u n i : ℝ) :=
      sub_nonneg.mpr (by exact_mod_cast hu n i)
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hResidual) hTime
  · norm_num
