-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord9_turn7_geometric_Standing_BV_uniform_B0_nonintegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:37:39.298383+00:00
-- url     : https://prove2.me/submissions/d03915ff-be72-4d64-919c-08767f12e204

import Mathlib
import Mathlib.Probability.Distributions.Geometric
import Theorems.Thm_AvramDividend_Classical_avram_a19_singular_geometric_transport_nonintegrable
import Theorems.Thm_AvramDividend_Classical_avram_coord9_turn6_original_Standing_BV_uniform_B0_nonintegrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A geometric law for the post-dividend reserve supplies the non-L1
    profile needed for the original Standing BV first cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q T x : ℝ) (hT : 0 < T)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hruin : ∀ ω, (0 : ℝ≥0∞) < ruinTime X x D ω)
    (hpositive : ∀ ω, 0 < x - rightLimit D 0 ω)
    (hcap : ∀ ω, ENNReal.ofReal (x - rightLimit D 0 ω) < C)
    (hmeas : AEStronglyMeasurable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P)
    (p : unitInterval) (hp : p != 0) (hhalf : (p : ℝ) = 1 / 2)
    (K : Ω → ℕ) (hK : MeasurePreserving K P (geometricMeasure p))
    (y : ℕ → ℝ)
    (hy : ∀ k, 0 < y k)
    (hsmall : ∀ k, y k ≤ 1 / 16)
    (hpower : ∀ k, y k ≤ 1 / ((2 : ℝ) ^ k) ^ 2)
    (hprofile : ∀ᵐ ω ∂P,
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω) =
      (3 : ℝ) + y (K ω) - 4 * Real.sqrt (y (K ω)) -
        2 / Real.sqrt (y (K ω)))
    (u : ℕ → ℕ → ℝ≥0) (B : ℕ → Ω → ℝ)
    (hgrid0 : ∀ n, u n 0 = 0)
    (huniform : ∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2))
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
  have hnonint : ¬ Integrable (fun ω =>
      X.generator w (x - rightLimit D 0 ω) -
        q * w (x - rightLimit D 0 ω)) P := by
    intro hsource
    have hscalar : Integrable (fun ω =>
        (3 : ℝ) + y (K ω) - 4 * Real.sqrt (y (K ω)) -
          2 / Real.sqrt (y (K ω))) P := by
      apply hsource.congr
      filter_upwards [hprofile] with ω hω
      exact hω
    have hneg : Integrable (fun ω =>
        -((3 : ℝ) + y (K ω) - 4 * Real.sqrt (y (K ω)) -
          2 / Real.sqrt (y (K ω)))) P := hscalar.neg
    exact (avram_a19_singular_geometric_transport_nonintegrable
      P p hp hhalf K hK y hy hsmall hpower) hneg
  exact avram_coord9_turn6_original_Standing_BV_uniform_B0_nonintegrable
    X hX hBV q T x hT w C D hruin hpositive hcap hmeas hnonint
    u B hgrid0 huniform hB
