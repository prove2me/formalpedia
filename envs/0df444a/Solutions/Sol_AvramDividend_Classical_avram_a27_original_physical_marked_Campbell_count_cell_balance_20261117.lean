-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_marked_Campbell_count_cell_balance_20261117
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:49:28.083973+00:00
-- url     : https://prove2.me/submissions/a583ec66-4832-4f14-a368-087501af3dad
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_mark_joint_pgf_exact_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_exponential_pgf_count_cell_coefficients_mecke_recurrence_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_marked_jump_pgf_exact_count_cell_series_20261117
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
    ∀ k : ℕ,
      (((k + 1 : ℕ) : ℝ) * (∫ ω in {ω : Ω | K ω = k + 1}, Real.exp (θ * J ω) ∂P)) =
        ((r : ℝ) + (t : ℝ) * (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν)) * (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P) := by
  classical
  let C : ℕ → ℝ := fun k =>
    ∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P
  let q : ℝ := ((r : ℝ) + (t : ℝ) * (∫ y in Iio (0 : ℝ), Real.exp (θ * y) - 1 ∂X.ν))
  have hPgf :=
    avram_a27_original_physical_negative_mark_joint_pgf_exact_20261117
      X hFinite hNu t ht θ hθ J hJMeas hJEq
      K r hK hLaw hCount hRate
  have hSeries (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
      HasSum (fun k : ℕ => z ^ k * C k)
        (Real.exp (q * z - (r : ℝ))) := by
    have hSource :=
      avram_a27_original_physical_negative_marked_jump_pgf_exact_count_cell_series_20261117
        X hFinite t θ (le_of_lt hθ) J hJMeas hJEq
        K hK z hz hz1
    rw [hPgf z hz hz1] at hSource
    simpa only [C, q] using hSource
  have hRec :=
    avram_a27_exponential_pgf_count_cell_coefficients_mecke_recurrence_20261117
      C (r : ℝ) q hSeries
  intro k
  simpa only [C, q] using hRec k
