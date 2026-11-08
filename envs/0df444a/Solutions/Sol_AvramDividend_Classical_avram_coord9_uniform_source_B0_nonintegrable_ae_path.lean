-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord9_uniform_source_B0_nonintegrable_ae_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:02:21.879038+00:00
-- url     : https://prove2.me/submissions/4a249462-71dc-485b-82b7-14f44700c92e

import Mathlib.Probability.Process.Filtration
import Theorems.Thm_AvramDividend_Classical_avram_coord9_uniform_B_zero_nonintegrable_of_ae_bv_jump_path
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The full original uniform-grid source formula forces a non-L1 first row
    when the genuine BV path and initial singular profile are present. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q T x : ℝ) (hT : 0 < T)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hruin : ∀ ω, (0 : ℝ≥0∞) < ruinTime X x D ω)
    (hpositive : ∀ ω, 0 < x - rightLimit D 0 ω)
    (hcap : ∀ ω, ENNReal.ofReal (x - rightLimit D 0 ω) < C)
    (hmeas : AEStronglyMeasurable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (hnonint : ¬ Integrable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (u : ℕ → ℕ → ℝ≥0) (B : ℕ → Ω → ℝ)
    (hgrid0 : ∀ n, u n 0 = 0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
    (hpath : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ((t : ℝ) * X.drift - X.X t ω) =
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0)
    (hB : ∀ n ω,
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
            else 0) * (R (u n i) - R (u n (i + 1))))) :
    ¬ Integrable (B 0) P := by
  let K : Ω → ℝ := fun ω =>
    let Z : ℕ → ℝ := fun i => Function.leftLim
      (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u 0 i)
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
      else 0
    let R : ℝ≥0 → ℝ := fun t =>
      ((t : ℝ) * X.drift - X.X t ω) - J t
    ∑ i ∈ Finset.range (0 + 1),
      (if (u 0 i : ℝ≥0∞) < ruinTime X x D ω ∧
          0 < Z i ∧ ENNReal.ofReal (Z i) < C then
        Real.exp (-(q * (u 0 i : ℝ))) * deriv w (Z i)
      else 0) * (R (u 0 i) - R (u 0 (i + 1)))
  have hK_def (ω : Ω) : K ω =
      (let Z : ℕ → ℝ := fun i => Function.leftLim
         (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) (u 0 i)
       let J : ℝ≥0 → ℝ := fun t =>
         ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
           Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
         else 0
       let R : ℝ≥0 → ℝ := fun t =>
         ((t : ℝ) * X.drift - X.X t ω) - J t
       ∑ i ∈ Finset.range (0 + 1),
         (if (u 0 i : ℝ≥0∞) < ruinTime X x D ω ∧
               0 < Z i ∧ ENNReal.ofReal (Z i) < C then
            Real.exp (-(q * (u 0 i : ℝ))) * deriv w (Z i)
          else 0) * (R (u 0 i) - R (u 0 (i + 1)))) := rfl
  have hB0 (ω : Ω) : B 0 ω =
      (let Z := Function.leftLim
         (fun t : ℝ≥0 => x + X.X t ω - rightLimit D t ω) 0
       if (0 : ℝ≥0∞) < ruinTime X x D ω ∧
           0 < Z ∧ ENNReal.ofReal Z < C then
         Real.exp (-(q * (0 : ℝ))) *
           (X.generator w Z - q * w Z) * (T / 2)
       else 0) + K ω := by
    have hb := hB 0 ω
    simpa only [K, Nat.zero_add, Finset.range_one, Finset.sum_singleton,
      hgrid0 0, huniform 0 1, Nat.cast_zero, Nat.cast_one,
      zero_add, zero_mul, one_mul, mul_one, zero_div, sub_zero,
      ENNReal.coe_zero, NNReal.coe_zero] using hb
  exact avram_coord9_uniform_B_zero_nonintegrable_of_ae_bv_jump_path
    X q T x hT w C D hruin hpositive hcap hmeas hnonint
    u B K hpath hK_def hB0
