-- Prove2me | solution 2 for AvramDividend.Classical.avram_a30_original_physical_negative_mark_conditional_Poisson_cell_Laplace_20261116
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:20:16.2701+00:00
-- url     : https://prove2.me/submissions/a95cc61e-404c-4f08-aae6-71bbfc451b3e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_positive_count_conditional_negative_mark_laplace_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_zero_count_laplace_cell_20261117
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
      (∀ k : ℕ,
        (∫ ω in {ω : Ω | K ω = k},
          Real.exp (θ * J ω) ∂P) =
          (poissonMeasure r).real {k} * m ^ k) ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) *
          (∫ y in Iio (0 : ℝ),
            Real.exp (θ * y) - 1 ∂X.ν) := by
  classical
  obtain ⟨m, hmInt, hPosCells, hRateM⟩ :=
    avram_a27_original_positive_count_conditional_negative_mark_laplace_20261117
      X hFinite hNu t ht θ hθ J hJMeas hJEq
      K r hK hLaw hCount hRate
  refine ⟨m, hmInt, ?_, hRateM⟩
  intro k
  by_cases hk : k = 0
  · subst k
    have h0 := avram_a27_original_physical_zero_count_laplace_cell_20261117
      X hFinite t θ J hJEq K r hK hLaw hCount
    simpa using h0
  · exact hPosCells k (Nat.pos_of_ne_zero hk)
