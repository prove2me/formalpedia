-- Prove2me | solution 1 for AvramDividend.Classical.avram_coord9_turn7_original_singular_geometric_generator_profile
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T23:30:06.079888+00:00
-- url     : https://prove2.me/submissions/fd229972-7ad1-458b-80e2-37df0d45ebdf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_a19_affine_singular_subunit_original_generator_eq
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual singular-density original generator evaluated at a geometric
    post-dividend reserve has the exact signed scalar HJB profile. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hν : X.ν = volume.withDensity (fun z : ℝ =>
      if z ∈ Ioo (-1 : ℝ) 0
      then ENNReal.ofReal (|z| ^ (-(3 / 2 : ℝ))) else 0))
    (hc : X.c = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (K : Ω → ℕ) (y : ℕ → ℝ)
    (hy : ∀ k, 0 < y k) (hsmall : ∀ k, y k ≤ 1 / 16)
    (hreserve : ∀ ω, x - rightLimit D 0 ω = y (K ω)) :
    ∀ ω, X.generator
        (fun u : ℝ => if u < 0 then (0 : ℝ) else 1 + u)
        (x - rightLimit D 0 ω) -
      (if x - rightLimit D 0 ω < 0 then (0 : ℝ)
        else 1 + (x - rightLimit D 0 ω)) =
      (3 : ℝ) + y (K ω) - 4 * Real.sqrt (y (K ω)) -
        2 / Real.sqrt (y (K ω)) := by
  intro ω
  rw [hreserve ω]
  have hz : 0 < y (K ω) := hy (K ω)
  have hz1 : y (K ω) < 1 := lt_of_le_of_lt (hsmall (K ω)) (by norm_num)
  have hn0 : ¬ y (K ω) < 0 := not_lt.mpr (le_of_lt hz)
  rw [if_neg hn0]
  rw [avram_a19_affine_singular_subunit_original_generator_eq X hBV hν
    (y (K ω)) hz hz1, hc]
  have hp : (y (K ω)) ^ (1 / 2 : ℝ) = Real.sqrt (y (K ω)) :=
    (Real.sqrt_eq_rpow _).symm
  have hn : (y (K ω)) ^ (-(1 / 2 : ℝ)) = (Real.sqrt (y (K ω)))⁻¹ := by
    rw [Real.rpow_neg (le_of_lt hz) (1 / 2 : ℝ)]
    rw [← Real.sqrt_eq_rpow _]
  have hratio : y (K ω) * (Real.sqrt (y (K ω)))⁻¹ =
      Real.sqrt (y (K ω)) := by
    simpa only [div_eq_mul_inv] using (Real.div_sqrt (x := y (K ω)))
  rw [hp, hn, div_eq_mul_inv]
  nlinarith [hratio]
