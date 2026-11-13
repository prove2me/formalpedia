-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_borel_simple_weighted_centered_mean_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:51:34.386549+00:00
-- url     : https://prove2.me/submissions/4b410e8b-9123-4a83-9f22-603dfddacde3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja35_original_negative_borel_real_count_first_moment
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (F : Finset ι) (B : ι → Set ℝ) (a : ι → ℝ)
    (hB : ∀ i ∈ F, MeasurableSet (B i))
    (hNeg : ∀ i ∈ F, B i ⊆ Iio (0 : ℝ)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ι → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ι → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i
    let Z : Ω → ℝ := fun ω => ∑ i ∈ F, a i * Y i ω
    Integrable Z P ∧ (∫ ω, Z ω ∂P) = 0 := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro NX r Y Z
  have hEach (i : ι) (hi : i ∈ F) :
      Integrable (Y i) P ∧ (∫ ω, Y i ω ∂P) = 0 := by
    have hBase : Integrable
        (fun ω => (NX ω (Ioc 0 T ×ˢ B i)).toReal) P ∧
        (∫ ω, (NX ω (Ioc 0 T ×ˢ B i)).toReal ∂P) = r i := by
      simpa only [NX, r] using
        (avram_ja35_original_negative_borel_real_count_first_moment
          X hFinite T (B i) (hB i hi) (hNeg i hi))
    have hInt : Integrable (Y i) P := by
      change Integrable
        (fun ω => (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i) P
      exact hBase.1.sub (integrable_const (r i))
    have hMean : (∫ ω, Y i ω ∂P) = 0 := by
      change (∫ ω, (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i ∂P) = 0
      rw [integral_sub hBase.1 (integrable_const (r i)), hBase.2]
      simp [MeasureTheory.Measure.real_def]
    exact ⟨hInt, hMean⟩
  have hTerm (i : ι) (hi : i ∈ F) :
      Integrable (fun ω => a i * Y i ω) P :=
    (hEach i hi).1.const_mul (a i)
  constructor
  · change Integrable (fun ω => ∑ i ∈ F, a i * Y i ω) P
    exact integrable_finset_sum F hTerm
  · change (∫ ω, ∑ i ∈ F, a i * Y i ω ∂P) = 0
    calc
      (∫ ω, ∑ i ∈ F, a i * Y i ω ∂P) =
          ∑ i ∈ F, (∫ ω, a i * Y i ω ∂P) :=
        integral_finset_sum F hTerm
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [integral_const_mul, (hEach i hi).2]
        ring
