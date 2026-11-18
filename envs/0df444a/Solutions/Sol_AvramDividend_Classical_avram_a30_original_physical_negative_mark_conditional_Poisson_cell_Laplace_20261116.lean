-- Prove2me | solution 1 for AvramDividend.Classical.avram_a30_original_physical_negative_mark_conditional_Poisson_cell_Laplace_20261116
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T15:36:52.912124+00:00
-- url     : https://prove2.me/submissions/89682910-cca8-47ff-8a80-22715460166a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_indep_poisson_count_cell_laplace_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a104_original_given_poisson_count_independent_physical_negative_mark_stream_20261114
import Theorems.Thm_AvramDividend_Classical_chat06_poisson_count_pgf_general
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Independence of a Poisson count and the original mark stream gives each count-cell Laplace integral. -/
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
  obtain ⟨Y, m, hY, hIndep, hJsum, hMom, hRateM⟩ :=
    avram_a104_original_given_poisson_count_independent_physical_negative_mark_stream_20261114
      X hFinite hNu t ht θ hθ J hJMeas hJEq K r hK hLaw hCount hRate
  have hpgf := chat06_poisson_count_pgf_general r m
  have hmInt : Integrable (fun k : ℕ => m ^ k) (poissonMeasure r) := by
    by_contra hn
    have hz : (∫ n : ℕ, m ^ n ∂poissonMeasure r) = 0 :=
      integral_undef hn
    rw [hz] at hpgf
    exact (Real.exp_ne_zero _) hpgf.symm
  refine ⟨m, hmInt, ?_, hRateM⟩
  intro k
  have hMarkCell := avram_a27_indep_poisson_count_cell_laplace_20261117 P K Y hK hY hIndep r hLaw θ m hMom k
  have hSet : MeasurableSet {ω : Ω | K ω = k} :=
    hK (measurableSet_singleton k)
  have hCong :
      ({ω : Ω | K ω = k}).indicator
        (fun ω => Real.exp (θ * J ω)) =ᵐ[P]
      ({ω : Ω | K ω = k}).indicator
        (fun ω => Real.exp
          (θ * ∑ j ∈ Finset.range (K ω), Y j ω)) := by
    filter_upwards [hJsum] with ω hω
    by_cases hk : K ω = k
    · simp [hk, hω]
    · simp [hk]
  calc
    _ = (∫ ω in {ω : Ω | K ω = k},
        Real.exp (θ * ∑ j ∈ Finset.range (K ω), Y j ω) ∂P) := by
          rw [← integral_indicator hSet, ← integral_indicator hSet]
          exact integral_congr_ae hCong
    _ = _ := hMarkCell
