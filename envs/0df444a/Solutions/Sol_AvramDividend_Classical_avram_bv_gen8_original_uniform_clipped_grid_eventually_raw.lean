-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_gen8_original_uniform_clipped_grid_eventually_raw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:50:35.11641+00:00
-- url     : https://prove2.me/submissions/eb1fe2bb-5f00-4ec8-80ac-da8e2ffab696

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
noncomputable section

/-- Each fixed physical BV generator grid has a pathwise finite clipping threshold. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ) (ω : Ω) :
    let Z : ℕ → ℝ := fun j => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
    let H : ℕ → ℝ := fun i =>
      if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u n i : ℝ))) *
          (X.generator w (Z i) - q * w (Z i)) *
          ((u n (i + 1) : ℝ) - (u n i : ℝ))
      else 0
    ∃ K0 : ℕ, ∀ K ≥ K0,
      (∑ i ∈ Finset.range (n + 1), max (-(K : ℝ)) (H i)) =
        ∑ i ∈ Finset.range (n + 1), H i := by
  let Z : ℕ → ℝ := fun j => Function.leftLim
    (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n j)
  let H : ℕ → ℝ := fun i =>
    if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
        0 < Z i ∧ ENNReal.ofReal (Z i) < C then
      Real.exp (-(q * (u n i : ℝ))) *
        (X.generator w (Z i) - q * w (Z i)) *
        ((u n (i + 1) : ℝ) - (u n i : ℝ))
    else 0
  change ∃ K0 : ℕ, ∀ K ≥ K0,
    (∑ i ∈ Finset.range (n + 1), max (-(K : ℝ)) (H i)) =
      ∑ i ∈ Finset.range (n + 1), H i
  obtain ⟨K0, hK0⟩ := exists_nat_gt (∑ i ∈ Finset.range (n + 1), |H i|)
  refine ⟨K0, ?_⟩
  intro K hK
  apply Finset.sum_congr rfl
  intro i hi
  rw [max_eq_right]
  have hpart : |H i| ≤ ∑ j ∈ Finset.range (n + 1), |H j| := by
    exact Finset.single_le_sum (fun j _ => abs_nonneg (H j)) hi
  have hcast : (K0 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hneg : -(K : ℝ) ≤ -( |H i|) := by linarith
  exact le_trans hneg (neg_abs_le (H i))
