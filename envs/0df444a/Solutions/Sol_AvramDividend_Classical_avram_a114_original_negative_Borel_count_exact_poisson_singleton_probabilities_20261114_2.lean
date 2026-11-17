-- Prove2me | solution 2 for AvramDividend.Classical.avram_a114_original_negative_Borel_count_exact_poisson_singleton_probabilities_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:01:47.675235+00:00
-- url     : https://prove2.me/submissions/30eb8920-b856-4357-9f4c-36ec041b55f3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a115_original_positive_rate_negative_Borel_count_poisson_singletons_20261114
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
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
  letI : IsProbabilityMeasure P := X.isProbability
  by_cases hrpos : 0 < r
  · exact avram_a115_original_positive_rate_negative_Borel_count_poisson_singletons_20261114
      X hFinite T B hB hNeg K hK hCount r hr hrpos
  · have hrzero : r = 0 := le_antisymm (le_of_not_gt hrpos) (zero_le)
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ B)
    have hFirst := avram_ja35_original_negative_borel_real_count_first_moment
      X hFinite T B hB hNeg
    have hCount' : (fun ω : Ω => (K ω : ℝ)) =ᵐ[P]
        (fun ω : Ω => (N ω).toReal) := hCount
    have hIntegrable : Integrable (fun ω : Ω => (K ω : ℝ)) P :=
      hFirst.1.congr hCount'.symm
    have hMean : (∫ ω, (K ω : ℝ) ∂P) = 0 := by
      calc
        (∫ ω, (K ω : ℝ) ∂P) = ∫ ω, (N ω).toReal ∂P :=
          integral_congr_ae hCount'
        _ = ((T : ℝ≥0∞) * X.ν B).toReal := hFirst.2
        _ = 0 := by rw [← hr, hrzero]; simp
    have hNonneg : (0 : Ω → ℝ) ≤ᵐ[P] (fun ω => (K ω : ℝ)) :=
      Filter.Eventually.of_forall (fun ω => Nat.cast_nonneg _)
    have hKzero : (fun ω : Ω => (K ω : ℝ)) =ᵐ[P] (fun _ => 0) :=
      (integral_eq_zero_iff_of_nonneg_ae hNonneg hIntegrable).mp hMean
    intro k
    have hs : {ω : Ω | K ω = k} =ᵐ[P]
        {ω : Ω | (0 : ℕ) = k} := by
      filter_upwards [hKzero] with ω hw
      have heq : K ω = 0 := by exact_mod_cast hw
      change (K ω = k) = ((0 : ℕ) = k)
      rw [heq]
    rw [hrzero]
    calc
      P {ω : Ω | K ω = k} = P {ω : Ω | (0 : ℕ) = k} := measure_congr hs
      _ = poissonMeasure 0 {k} := by
        cases k with
        | zero => simp [poissonMeasure_singleton]
        | succ k => simp [poissonMeasure_singleton]
