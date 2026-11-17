-- Prove2me | solution 1 for AvramDividend.Classical.avram_a25_original_negative_Borel_binomial_grid_singleton_approx_20261115
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:30:56.718649+00:00
-- url     : https://prove2.me/submissions/41dd7302-0896-47ae-95d9-da7e6ebda8ec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_Borel_occupied_grid_binomial_law_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_physical_occupied_grid_count_measurable_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_Borel_occupancy_disagreement_probability_vanishes_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a26_physical_void_probability_parameter_rate_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a26_source_count_coupling_implies_singleton_law_limit_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a26_finite_ENNReal_tendsto_from_real_cast_20261116
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
    ∃ p : ℕ → unitInterval,
      Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ))
        atTop (𝓝 (r : ℝ)) ∧
      ∀ k : ℕ, Tendsto (fun n : ℕ => Bin(n, p n) {k})
        atTop (𝓝 (P.map K {k})) := by
  letI : IsProbabilityMeasure P := X.isProbability
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let δ : ℕ → ℝ≥0 := fun n => T / (n : ℝ≥0)
  let Z : ℕ → Ω → ℕ := fun n ω =>
    ((Finset.range n).filter (fun i : ℕ =>
      NX ω (Ioc ((i : ℝ≥0) * δ n)
        (((i + 1 : ℕ) : ℝ≥0) * δ n) ×ˢ B) ≠ 0)).card
  obtain ⟨p, hp, hLaw⟩ :=
    avram_a26_original_Borel_occupied_grid_binomial_law_20261116
      X hFinite T B hB hNeg
  have hp' : ∀ n : ℕ, (p n : ℝ) =
      1 - (P {ω : Ω | NX ω (Ioc 0 (δ n) ×ˢ B) = 0}).toReal := by
    simpa only [NX, δ] using hp
  have hLaw' : ∀ n, P.map (Z n) = Bin(n, p n) := by
    simpa only [NX, δ, Z] using hLaw
  have hMeas : ∀ n : ℕ, Measurable (Z n) := by
    simpa only [NX, δ, Z] using
      (avram_a26_original_physical_occupied_grid_count_measurable_20261116
        X T B hB)
  have hBad : Tendsto (fun n : ℕ =>
      (P {ω : Ω | K ω ≠ Z n ω}).toReal) atTop (𝓝 (0 : ℝ)) := by
    simpa only [NX, δ, Z] using
      (avram_a26_original_Borel_occupancy_disagreement_probability_vanishes_20261116
        X hFinite T B hB hNeg K hK hCount)
  have hRate : Tendsto (fun n : ℕ => (n : ℝ) * (p n : ℝ))
      atTop (𝓝 ((T : ℝ) * (X.ν B).toReal)) := by
    apply avram_a26_physical_void_probability_parameter_rate_20261116
      X hFinite T B hB hNeg p
    intro n
    simpa only [NX, δ] using hp' n
  have hRateEq : ((T : ℝ) * (X.ν B).toReal) = (r : ℝ) := by
    rw [hr]
    simp only [ENNReal.toReal_mul, ENNReal.coe_toReal]
  refine ⟨p, ?_, ?_⟩
  · simpa only [hRateEq] using hRate
  · intro k
    have hReal := avram_a26_source_count_coupling_implies_singleton_law_limit_20261116
      P K hK Z hMeas p hLaw' hBad k
    apply avram_a26_finite_ENNReal_tendsto_from_real_cast_20261116
      (fun n : ℕ => Bin(n, p n) {k}) (P.map K {k})
    · intro n
      exact measure_ne_top _ _
    · exact measure_ne_top _ _
    · exact hReal
