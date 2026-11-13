-- Prove2me | solution 1 for AvramDividend.Classical.avram_a20_original_disjoint_borel_simple_raw_weighted_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T18:51:45.010511+00:00
-- url     : https://prove2.me/submissions/20049249-ab8d-41a3-b63a-9e4dae2beb8d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_borel_simple_weighted_centered_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_ja31_original_finite_borel_mark_source_isometry
import Theorems.Thm_AvramDividend_Classical_avram_a20_real_source_centered_square_shift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (F : Finset ι) (B : ι → Set ℝ) (a : ι → ℝ)
    (hB : ∀ i ∈ F, MeasurableSet (B i))
    (hNeg : ∀ i ∈ F, B i ⊆ Iio (0 : ℝ))
    (hDisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ι → ℝ := fun i => ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let J : Ω → ℝ := fun ω =>
      ∑ i ∈ F, a i * (NX ω (Ioc 0 T ×ˢ B i)).toReal
    let m : ℝ := ∑ i ∈ F, a i * r i
    let v : ℝ := ∑ i ∈ F, (a i) ^ 2 * r i
    Integrable J P ∧ Integrable (fun ω => (J ω) ^ 2) P ∧
      (∫ ω, J ω ∂P) = m ∧
      (∫ ω, (J ω) ^ 2 ∂P) = m ^ 2 + v := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro NX r J m v
  let Y : ι → Ω → ℝ := fun i ω =>
    (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i
  let Z : Ω → ℝ := fun ω => ∑ i ∈ F, a i * Y i ω
  have hZ : Integrable Z P ∧ (∫ ω, Z ω ∂P) = 0 := by
    simpa only [NX, r, Y, Z] using
      (avram_a20_original_borel_simple_weighted_centered_mean_zero
        X hFinite T F B a hB hNeg)
  have hZsq : Integrable (fun ω => (Z ω) ^ 2) P ∧
      (∫ ω, (Z ω) ^ 2 ∂P) = v := by
    simpa only [NX, r, Y, Z, v] using
      (avram_ja31_original_finite_borel_mark_source_isometry
        X hFinite T F B a hB hNeg hDisj)
  have hShift :=
    avram_a20_real_source_centered_square_shift P Z m v
      hZ.1 hZsq.1 hZ.2 hZsq.2
  have hEq : J = fun ω => Z ω + m := by
    funext ω
    change (∑ i ∈ F, a i * (NX ω (Ioc 0 T ×ˢ B i)).toReal) =
      (∑ i ∈ F, a i *
        ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)) +
      ∑ i ∈ F, a i * r i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hJI : Integrable J P := by
    rw [hEq]
    exact hZ.1.add (integrable_const m)
  have hJ2 : Integrable (fun ω => (J ω) ^ 2) P := by
    simpa only [hEq] using hShift.1
  refine ⟨hJI, hJ2, ?_, ?_⟩
  · rw [hEq, integral_add hZ.1 (integrable_const m), hZ.2]
    simp [MeasureTheory.Measure.real_def]
  · calc
      (∫ ω, (J ω) ^ 2 ∂P) =
          (∫ ω, (Z ω + m) ^ 2 ∂P) := by rw [hEq]
      _ = v + m ^ 2 := hShift.2
      _ = m ^ 2 + v := by ring
