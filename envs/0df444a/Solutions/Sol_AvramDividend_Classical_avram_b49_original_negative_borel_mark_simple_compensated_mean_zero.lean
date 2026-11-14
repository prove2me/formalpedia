-- Prove2me | solution 1 for AvramDividend.Classical.avram_b49_original_negative_borel_mark_simple_compensated_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T09:57:38.420896+00:00
-- url     : https://prove2.me/submissions/ea289323-9371-4d15-9f48-4edb298a7daf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Original finite marked jump-count stochastic simple gain is integrable and centred. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (K : ℕ) (B : ℕ → Set ℝ) (c : ℕ → ℝ)
    (hB : ∀ i ∈ Finset.range K, MeasurableSet (B i))
    (hNeg : ∀ i ∈ Finset.range K, B i ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let F : Ω → ℝ := fun ω =>
      ∑ i ∈ Finset.range K,
        c i * ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
          ((t : ℝ≥0∞) * X.ν (B i)).toReal)
    Integrable F P ∧ (∫ ω, F ω ∂P) = 0 := by 
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  dsimp only
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hCell (i : ℕ) (hi : i ∈ Finset.range K) :
      Integrable (fun ω =>
        c i * ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
          ((t : ℝ≥0∞) * X.ν (B i)).toReal)) P ∧
      (∫ ω, c i * ((NX ω (Ioc 0 t ×ˢ B i)).toReal -
          ((t : ℝ≥0∞) * X.ν (B i)).toReal) ∂P) = 0 := by
    obtain ⟨hRawI, hRawMean⟩ :=
      avram_ja35_original_negative_borel_real_count_first_moment
        X hFinite t (B i) (hB i hi) (hNeg i hi)
    dsimp only at hRawI hRawMean
    have hCI : Integrable (fun ω =>
        (NX ω (Ioc 0 t ×ˢ B i)).toReal -
          ((t : ℝ≥0∞) * X.ν (B i)).toReal) P :=
      hRawI.sub (integrable_const _)
    refine ⟨hCI.const_mul _, ?_⟩
    rw [integral_const_mul]
    rw [integral_sub hRawI (integrable_const _)]
    rw [hRawMean]
    simp
  constructor
  · exact integrable_finset_sum (Finset.range K)
      (fun i hi => (hCell i hi).1)
  · rw [integral_finset_sum (Finset.range K)
      (fun i hi => (hCell i hi).1)]
    exact Finset.sum_eq_zero (fun i hi => (hCell i hi).2)
