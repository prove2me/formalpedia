-- Prove2me | solution 3 for AvramDividend.Classical.avram_a30_original_physical_negative_mark_conditional_Poisson_cell_Laplace_20261116
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:40:18.048894+00:00
-- url     : https://prove2.me/submissions/ccac6a79-c7f5-432d-9ab3-e61b30581861
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_mark_cell_mecke_recursion_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_zero_count_laplace_cell_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_marked_poisson_count_cell_recursion_factorisation_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_poisson_singleton_real_rate_recursion_20261117
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- The original physical count-cell Mecke recursion and source zero-cell identity imply all conditional mark moments. -/
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
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨m, hm0, hm1, hRateM, hRec⟩ :=
    avram_a27_original_physical_negative_mark_cell_mecke_recursion_20261117
      X hFinite hNu t ht θ hθ J hJMeas hJEq
      K r hK hLaw hCount hRate
  have hpgf := chat06_poisson_count_pgf_general r m
  have hmInt : Integrable (fun k : ℕ => m ^ k) (poissonMeasure r) := by
    by_contra hn
    have hz : (∫ n : ℕ, m ^ n ∂poissonMeasure r) = 0 :=
      integral_undef hn
    rw [hz] at hpgf
    exact (Real.exp_ne_zero _) hpgf.symm
  have hZero :=
    avram_a27_original_physical_zero_count_laplace_cell_20261117
      X hFinite t θ J hJEq K r hK hLaw hCount
  have hAll :=
    avram_a27_marked_poisson_count_cell_recursion_factorisation_20261117
      (r : ℝ) m
      (fun k : ℕ => ∫ ω in {ω : Ω | K ω = k},
        Real.exp (θ * J ω) ∂P)
      (fun k : ℕ => (poissonMeasure r).real {k})
      hZero
      (fun k => avram_a27_poisson_singleton_real_rate_recursion_20261117 r k)
      hRec
  exact ⟨m, hmInt, hAll, hRateM⟩
