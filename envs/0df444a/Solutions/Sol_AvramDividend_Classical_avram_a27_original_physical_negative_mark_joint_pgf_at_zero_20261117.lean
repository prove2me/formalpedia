-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_negative_mark_joint_pgf_at_zero_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:43:57.112323+00:00
-- url     : https://prove2.me/submissions/cd8e76bb-af0f-494e-8683-281c8906b6b3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_zero_count_laplace_cell_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- At the zero PGF argument, the original physical marked-count Laplace expectation is the zero-cell Poisson mass. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
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
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal) :
    (∫ ω, (0 : ℝ) ^ (K ω) * Real.exp (θ * J ω) ∂P) =
      (poissonMeasure r).real {0} := by
  have hZero :=
    avram_a27_original_physical_zero_count_laplace_cell_20261117
      X hFinite t θ J hJEq K r hK hLaw hCount
  have hSet : MeasurableSet {ω : Ω | K ω = 0} :=
    hK (measurableSet_singleton 0)
  calc
    (∫ ω, (0 : ℝ) ^ K ω * Real.exp (θ * J ω) ∂P) =
        (∫ ω in {ω : Ω | K ω = 0}, Real.exp (θ * J ω) ∂P) := by
      rw [← integral_indicator hSet]
      congr 1
      funext ω
      by_cases hk : K ω = 0
      · simp [hk, Set.indicator_of_mem hk]
      · simp [hk, Set.indicator_of_notMem hk]
    _ = (poissonMeasure r).real {0} := hZero
