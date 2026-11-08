-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord9_turn7_original_singular_Standing_BV_B0_nonintegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:51:31.607668+00:00
-- url     : https://prove2.me/submissions/c0a4a056-381f-445c-ad46-45e559676ad0

import Mathlib
import Mathlib.Probability.Distributions.Geometric
import Theorems.Thm_AvramDividend_Classical_avram_coord9_turn7_original_singular_geometric_generator_profile
import Theorems.Thm_AvramDividend_Classical_avram_coord9_turn7_geometric_Standing_BV_uniform_B0_nonintegrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original singular Lévy triplet and geometric postpayment reserve
    imply failure of L1 in the exact Standing BV first physical grid cell. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q T x : ℝ) (hT : 0 < T)
    (w : ℝ → ℝ)
    (hq : q = 1)
    (hw : w = (fun z : ℝ => if z < 0 then 0 else 1 + z))
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
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
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0)
    (hreserve : ∀ ω, x - rightLimit D 0 ω = y (K ω))
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
  apply avram_coord9_turn7_geometric_Standing_BV_uniform_B0_nonintegrable
    X hX hBV q T x hT w C D hruin hpositive hcap hmeas
    p hp hhalf K hK y hy hsmall hpower ?_ u B hgrid0 huniform hB
  filter_upwards [] with ω
  rw [hq, hw]
  simpa only [one_mul] using
    (avram_coord9_turn7_original_singular_geometric_generator_profile
      X hBV hν hc x D K y hy hsmall hreserve ω)
