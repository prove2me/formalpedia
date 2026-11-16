-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_original_uniform_grid_exists_exact_B_nonpositive_and_true_prepayment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:14:11.526082+00:00
-- url     : https://prove2.me/submissions/033e7444-f249-4add-b247-63905946d52a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb_original_strict_uniform_grid_HJB_B_nonpos_and_prepayment_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (T : ℝ) (hT : 0 < T)
    (u : ℕ → ℕ → ℝ≥0)
    (hMono : ∀ n i, u n i ≤ u n (i + 1))
    (hUniform : ∀ n i, (u n i : ℝ) =
      T * (i : ℝ) / ((n : ℝ) + 2)) :
    ∃ B : ℕ → Ω → ℝ,
    (∀ n ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      B n ω =
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
           else 0) * (R (u n i) - R (u n (i + 1))))) ∧
    (∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0) ∧
    (∀ᵐ ω ∂P, ∀ n i,
      Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω)
        (u n (i + 1)) =
      riskProcess X x D (u n (i + 1)) ω) := by
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
  have hBEq : ∀ n ω,
      let Z : ℕ → ℝ := fun i => Function.leftLim
        (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u n i)
      B n ω =
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
           else 0) * (R (u n i) - R (u n (i + 1)))) := by
    intro n ω
    rfl
  have hBoth :=
    avram_bvb_original_strict_uniform_grid_HJB_B_nonpos_and_prepayment_ae
      X hX hBV q w C hw x D u hMono hD T hT hUniform
  have hAllB : ∀ᵐ ω ∂P, ∀ n : ℕ, B n ω ≤ 0 := by
    simpa only [B] using hBoth.1
  exact ⟨B, hBEq, hAllB, hBoth.2⟩
