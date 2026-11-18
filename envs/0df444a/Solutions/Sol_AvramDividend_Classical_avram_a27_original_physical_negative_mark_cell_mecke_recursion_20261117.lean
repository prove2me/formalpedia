-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_negative_mark_cell_mecke_recursion_20261117
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:02:16.489198+00:00
-- url     : https://prove2.me/submissions/571d7067-2209-49e0-9dbc-57c1a76d3fa4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_marked_Campbell_count_cell_balance_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_clock_mark_laplace_exact_rate_20261117
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
      ∑' u : ℝ≥0,
        if 0 < u ∧ u ≤ t then
          X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
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
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ),
            Real.exp (θ * y) - 1 ∂X.ν) ∧
      (∀ k : ℕ,
        (∫ ω in {ω : Ω | K ω = k + 1},
          Real.exp (θ * J ω) ∂P) =
        m * ((r : ℝ) / ((k + 1 : ℕ) : ℝ)) *
          (∫ ω in {ω : Ω | K ω = k},
            Real.exp (θ * J ω) ∂P)) := by
  classical
  obtain ⟨m, hm0, hm1, hRateM⟩ :=
    avram_a27_original_physical_clock_mark_laplace_exact_rate_20261117
      X hFinite hNu t θ (le_of_lt hθ) r hRate
  refine ⟨m, hm0, hm1, hRateM, ?_⟩
  intro k
  have hCampbell :=
    avram_a27_original_physical_marked_Campbell_count_cell_balance_20261117
      X hFinite hNu t ht θ hθ J hJMeas hJEq
      K r hK hLaw hCount hRate k
  have hScalar : (r : ℝ) + (t : ℝ) *
      (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν) = (r : ℝ) * m := by
    rw [← hRateM]
    ring
  have hkNe : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hkNe)
  calc
    (((k + 1 : ℕ) : ℝ)) * (∫ ω in {ω : Ω | K ω = k + 1}, Real.exp (θ * J ω) ∂P) =
        ((r : ℝ) + (t : ℝ) * (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) * (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P) := hCampbell
    _ = ((r : ℝ) * m) * (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P) := by rw [hScalar]
    _ = (((k + 1 : ℕ) : ℝ)) *
        (m * ((r : ℝ) / ((k + 1 : ℕ) : ℝ)) * (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P)) := by
      field_simp
