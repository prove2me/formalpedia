-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_positive_count_conditional_negative_mark_laplace_20261117
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:40:16.751628+00:00
-- url     : https://prove2.me/submissions/093e46cf-086b-4b77-92cd-4f1ba72cc5ba
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_mark_cell_mecke_recursion_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_zero_count_laplace_cell_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_marked_poisson_count_cell_recursion_factorisation_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_poisson_singleton_real_rate_recursion_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_poisson_real_geometric_sequence_integrable_20261117
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
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
    ∃ m : ℝ,
      Integrable (fun k : ℕ => m ^ k) (poissonMeasure r) ∧
      (∀ k : ℕ, 0 < k →
        (∫ ω in {ω : Ω | K ω = k},
          Real.exp (θ * J ω) ∂P) =
          (poissonMeasure r).real {k} * m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ),
            Real.exp (θ * y) - 1 ∂X.ν) := by
  classical
  let C : ℕ → ℝ :=
    fun k => ∫ ω in {ω : Ω | K ω = k},
      Real.exp (θ * J ω) ∂P
  let M : ℕ → ℝ :=
    fun k => (poissonMeasure r).real {k}
  obtain ⟨m, hLow, hHigh, hRateM, hStep⟩ :=
    avram_a27_original_physical_negative_mark_cell_mecke_recursion_20261117
      X hFinite hNu t ht θ hθ J hJMeas hJEq
      K r hK hLaw hCount hRate
  have h0 : C 0 = M 0 :=
    avram_a27_original_physical_zero_count_laplace_cell_20261117
      X hFinite t θ J hJEq K r hK hLaw hCount
  have hMass : ∀ k : ℕ,
      M (k + 1) = ((r : ℝ) / ((k + 1 : ℕ) : ℝ)) * M k :=
    avram_a27_poisson_singleton_real_rate_recursion_20261117 r
  have hMarked : ∀ k : ℕ,
      C (k + 1) = m * ((r : ℝ) / ((k + 1 : ℕ) : ℝ)) * C k :=
    hStep
  have hCells := avram_a27_marked_poisson_count_cell_recursion_factorisation_20261117
    (r : ℝ) m C M h0 hMass hMarked
  have hmInt :=
    avram_a27_poisson_real_geometric_sequence_integrable_20261117 r m
  exact ⟨m, hmInt, (fun k _ => hCells k), hRateM⟩
