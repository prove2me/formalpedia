-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva34_original_B_nonpositive_mean_of_full_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T21:44:05.501203+00:00
-- url     : https://prove2.me/submissions/c84b26fb-fe8d-4711-ae47-cc08905f615e

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_original_B_positivepart_integrable_zero
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (u : ℕ → ℕ → ℝ≥0)
    (hmono : ∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) :
    let B : ℕ → Ω → ℝ := fun n ω =>
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      (∑ i ∈ Finset.range (n + 1),
        if (u n i : ℝ≥0∞) < ruinTime X x D ω ∧
            0 < Z i ∧ ENNReal.ofReal (Z i) < C then
          Real.exp (-(q * (u n i : ℝ))) *
            (X.generator w (Z i) - q * w (Z i)) *
            ((u n (i + 1) : ℝ) - (u n i : ℝ))
        else 0) +
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
          else 0) * (R (u n i) - R (u n (i + 1))))
    (∀ n, Integrable (B n) P) →
      ∀ n, (∫ ω, B n ω ∂P) ≤ 0 := by
  intro B hBI n
  have hMax : Integrable (fun ω => max (B n ω) 0) P ∧
      (∫ ω, max (B n ω) 0 ∂P) = 0 := by
    simpa only using
      (avram_bv_residual9_original_B_positivepart_integrable_zero
        X hBV q w C hw_gen hw_grad x D u hmono n)
  calc
    (∫ ω, B n ω ∂P) ≤ (∫ ω, max (B n ω) 0 ∂P) := by
      exact integral_mono (hBI n) hMax.1 (fun ω => le_max_left _ _)
    _ = 0 := hMax.2
