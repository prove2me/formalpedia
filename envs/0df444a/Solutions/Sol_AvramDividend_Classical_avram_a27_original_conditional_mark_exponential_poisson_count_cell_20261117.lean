-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_conditional_mark_exponential_poisson_count_cell_20261117
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T22:09:02.655014+00:00
-- url     : https://prove2.me/submissions/06f9f324-2b73-410e-a792-109f5df40bfa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_AvramDividend_Classical_avram_a27_original_iid_negative_mark_stream_source_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_indep_poisson_count_cell_laplace_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_clock_mark_laplace_exact_rate_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_poisson_count_rate_real_clock_product_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_nonzero_negative_mark_rate_real_positive_20261117
import Mathlib
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
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      (r : ℝ) * (m - 1) =
        (t : ℝ) * (∫ y in Iio (0 : ℝ),
          Real.exp (θ * y) - 1 ∂X.ν) ∧
      ∀ k : ℕ,
        (∫ ω in {ω : Ω | K ω = k},
          Real.exp (θ * J ω) ∂P) =
        (poissonMeasure r).real {k} * m ^ k := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨Y, m, hY, hKY, hIID, hSame, hJ, hMom, hRateM⟩ :=
    avram_a27_original_iid_negative_mark_stream_source_20261117
      X hFinite hNu t ht θ hθ J hJMeas hJEq K r hK hLaw hCount hRate
  obtain ⟨m0, hm0, hm1, hRate0⟩ :=
    avram_a27_original_physical_clock_mark_laplace_exact_rate_20261117
      X hFinite hNu t θ (le_of_lt hθ) r hRate
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    rw [hRate, avram_a27_original_physical_poisson_count_rate_real_clock_product_20261117]
    have ht' : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    exact mul_pos ht'
      (avram_a27_original_nonzero_negative_mark_rate_real_positive_20261117
        X hFinite hNu)
  have hmEq : m = m0 := by
    have hmul : (r : ℝ) * (m - m0) = 0 := by linarith [hRateM, hRate0]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (ne_of_gt hrpos))
  refine ⟨m, ?_, ?_, hRateM, ?_⟩
  · simpa only [hmEq] using hm0
  · simpa only [hmEq] using hm1
  · intro k
    have hSet : MeasurableSet {ω : Ω | K ω = k} :=
      hK (measurableSet_singleton k)
    calc
      (∫ ω in {ω : Ω | K ω = k}, Real.exp (θ * J ω) ∂P) =
        (∫ ω in {ω : Ω | K ω = k},
          Real.exp (θ * ∑ j ∈ Finset.range (K ω), Y j ω) ∂P) := by
          apply setIntegral_congr_ae hSet
          filter_upwards [hJ] with ω hω _
          rw [hω]
      _ = (poissonMeasure r).real {k} * m ^ k :=
        avram_a27_indep_poisson_count_cell_laplace_20261117
          P K Y hK hY hKY r hLaw θ m hMom k
