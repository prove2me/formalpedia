-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_negative_mark_joint_pgf_exact_20261117
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T21:33:47.437356+00:00
-- url     : https://prove2.me/submissions/dee4f9ab-d03d-45c2-a677-c2e85df66d04
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Distributions.Poisson.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_conditional_mark_exponential_poisson_count_cell_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_marked_jump_pgf_exact_count_cell_series_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_real_exponential_weighted_poisson_coefficient_hasSum_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (hNu : X.ν ≠ 0)
    (t : ℝ≥0) (ht : 0 < t) (θ : ℝ) (hθ : 0 < θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (r : ℝ≥0)
    (hK : Measurable K) (hLaw : HasLaw K (poissonMeasure r) P)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal)
    (hRate : (r : ℝ) =
      ((t : ℝ≥0∞) * X.ν (Iio (0 : ℝ))).toReal) :
    ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
      (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) =
        Real.exp (((r : ℝ) +
          (t : ℝ) * (∫ y in Iio (0 : ℝ),
            Real.exp (θ * y) - 1 ∂X.ν)) * z - (r : ℝ)) := by
  obtain ⟨m, hm0, hm1, hmRate, hCell⟩ :=
    avram_a27_original_conditional_mark_exponential_poisson_count_cell_20261117
      X hFinite hNu t ht θ hθ J hJMeas hJEq K r hK hLaw hCount hRate
  intro z hz hz1
  have hCoeff (k : ℕ) :
      (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P) =
        Real.exp (-(r : ℝ)) *
          (((r : ℝ) * m) ^ k / (k.factorial : ℝ)) := by
    rw [hCell k, ProbabilityTheory.poissonMeasure_real_singleton]
    rw [mul_pow]
    ring
  have hSeries :=
    avram_a27_original_physical_negative_marked_jump_pgf_exact_count_cell_series_20261117
      X hFinite t θ (le_of_lt hθ) J hJMeas hJEq K hK z hz hz1
  have hSeries' :
      HasSum (fun k : ℕ => z ^ k *
        (Real.exp (-(r : ℝ)) *
          (((r : ℝ) * m) ^ k / (k.factorial : ℝ))))
        (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) := by
    simpa only [hCoeff] using hSeries
  have hExp :=
    avram_a27_real_exponential_weighted_poisson_coefficient_hasSum_20261117
      (r : ℝ) ((r : ℝ) * m) z
  have hBase :
      (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) =
        Real.exp (((r : ℝ) * m) * z - (r : ℝ)) :=
    hSeries'.unique hExp
  have hq :
      (r : ℝ) * m = (r : ℝ) +
        (t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) := by
    calc
      (r : ℝ) * m = (r : ℝ) * (m - 1) + (r : ℝ) := by ring
      _ = (t : ℝ) * (∫ y in Iio (0 : ℝ),
            Real.exp (θ * y) - 1 ∂X.ν) + (r : ℝ) := by rw [hmRate]
      _ = _ := by ring
  calc
    (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) =
        Real.exp (((r : ℝ) * m) * z - (r : ℝ)) := hBase
    _ = _ := by rw [hq]
