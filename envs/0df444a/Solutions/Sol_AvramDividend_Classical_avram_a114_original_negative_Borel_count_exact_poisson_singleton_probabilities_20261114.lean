-- Prove2me | solution 1 for AvramDividend.Classical.avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:26:06.833315+00:00
-- url     : https://prove2.me/submissions/1d5435e1-c7ed-415f-8340-1746e8da60fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
import Theorems.Thm_AvramDividend_Classical_avram_a115_original_positive_rate_negative_Borel_count_poisson_singletons_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : Set ℝ)
    (hB : MeasurableSet B) (hNeg : B ⊆ Iio (0 : ℝ))
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)).toReal)
    (r : ℝ≥0)
    (hr : (r : ℝ) = ((T : ℝ≥0∞) * X.ν B).toReal) :
    ∀ k : ℕ, P {ω : Ω | K ω = k} = poissonMeasure r {k} := by
  by_cases hrZero : r = 0
  · let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    have hFirst :
        Integrable (fun ω => (N ω).toReal) P ∧
        (∫ ω, (N ω).toReal ∂P) =
          ((T : ℝ≥0∞) * X.ν B).toReal := by
      simpa only [N] using
        avram_ja35_original_negative_borel_real_count_first_moment
          X hFinite T B hB hNeg
    have hNonneg : 0 ≤ᵐ[P] (fun ω => (N ω).toReal) :=
      Filter.Eventually.of_forall (fun ω => ENNReal.toReal_nonneg)
    have hMeanZero : (∫ ω, (N ω).toReal ∂P) = 0 := by
      rw [hFirst.2, ← hr, hrZero]
      rfl
    have hNAe : (fun ω => (N ω).toReal) =ᵐ[P]
        (fun _ => (0 : ℝ)) :=
      (integral_eq_zero_iff_of_nonneg_ae hNonneg hFirst.1).mp hMeanZero
    have hKAe : K =ᵐ[P] (fun _ : Ω => (0 : ℕ)) := by
      filter_upwards [hCount, hNAe] with ω hKω hNω
      have hz : (K ω : ℝ) = 0 := hKω.trans hNω
      exact_mod_cast hz
    letI : IsProbabilityMeasure P := X.isProbability
    have hMapZero : Measure.map K P = Measure.dirac (0 : ℕ) := calc
      Measure.map K P =
          Measure.map (fun _ : Ω => (0 : ℕ)) P :=
        Measure.map_congr hKAe
      _ = Measure.dirac 0 := by simp
    have hPoissonZero : poissonMeasure (0 : ℝ≥0) = Measure.dirac (0 : ℕ) := by
      refine Measure.ext_of_singleton fun n => ?_
      rw [poissonMeasure_singleton, Measure.dirac_apply' 0 (measurableSet_singleton n)]
      by_cases hn : n = 0
      · subst hn
        simp
      · simp only [Set.indicator_apply, Set.mem_singleton_iff, Pi.one_apply, NNReal.coe_zero]
        rw [if_neg (fun h => hn h.symm)]
        simp [zero_pow hn]
    have hPoisson : Measure.map K P = poissonMeasure r := by
      rw [hrZero]
      simpa only [hPoissonZero] using hMapZero
    intro k
    have hEvent := congrArg (fun μ : Measure ℕ => μ {k}) hPoisson
    rw [Measure.map_apply hK (measurableSet_singleton k)] at hEvent
    exact hEvent
  · have hPositive : 0 < r :=
      lt_of_le_of_ne (by positivity : 0 ≤ r) (Ne.symm hrZero)
    exact
      avram_a115_original_positive_rate_negative_Borel_count_poisson_singletons_20261114
        X hFinite T B hB hNeg K hK hCount r hr hPositive
