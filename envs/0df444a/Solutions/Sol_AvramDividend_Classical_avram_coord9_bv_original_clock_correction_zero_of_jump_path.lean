-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord9_bv_original_clock_correction_zero_of_jump_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T19:07:29.397535+00:00
-- url     : https://prove2.me/submissions/2c5ef622-9036-4a3c-870e-3d7c03fdee8f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q x : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0) (Z : ℕ → ℝ)
    (hpath : ∀ t : ℝ≥0,
      ((t : ℝ) * X.drift - X.X t ω) =
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) :
    ∀ n : ℕ,
      (let J : ℝ≥0 → ℝ := fun t =>
         ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
           Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
         else 0
       let R : ℝ≥0 → ℝ := fun t =>
         ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (n + 1),
         (if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u n i : ℝ))) * deriv w (Z i)
          else 0) * (R (u n i) - R (u n (i + 1)))) = 0 := by
  intro n
  have hR (t : ℝ≥0) :
      ((t : ℝ) * X.drift - X.X t ω) -
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = 0 := by
    rw [hpath t]
    exact sub_self _
  dsimp only
  simp only [hR, sub_self, mul_zero, Finset.sum_const_zero]
