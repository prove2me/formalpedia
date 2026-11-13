-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_original_disjoint_borel_weighted_centered_energy_20261112
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T23:44:11.840922+00:00
-- url     : https://prove2.me/submissions/e265e6fa-2476-4ba5-b7a1-780d04310f41

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_disjoint_borel_simple_raw_weighted_second_moment
import Theorems.Thm_AvramDividend_Classical_avram_a21_raw_second_centered_variance_20261112
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- Centred disjoint physical Borel marked cells have exact Poisson energy. -/
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
    let Z : Ω → ℝ := fun ω =>
      ∑ i ∈ F, a i * ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
    let v : ℝ := ∑ i ∈ F, (a i) ^ 2 * r i
    Integrable (fun ω => (Z ω) ^ 2) P ∧
      (∫ ω, (Z ω) ^ 2 ∂P) = v := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
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
  let Z : Ω → ℝ := fun ω =>
    ∑ i ∈ F, a i * ((NX ω (Ioc 0 T ×ˢ B i)).toReal - r i)
  change Integrable (fun ω => (Z ω) ^ 2) P ∧
    (∫ ω, (Z ω) ^ 2 ∂P) = v
  have hRaw := avram_a20_original_disjoint_borel_simple_raw_weighted_second_moment
    X hFinite T F B a hB hNeg hDisj
  change Integrable J P ∧ Integrable (fun ω => (J ω) ^ 2) P ∧
    (∫ ω, J ω ∂P) = m ∧
    (∫ ω, (J ω) ^ 2 ∂P) = m ^ 2 + v at hRaw
  rcases hRaw with ⟨hJ, hJ2, hMean, hSecond⟩
  have hZ : ∀ ω, Z ω = J ω - m := by
    intro ω
    simp only [Z, J, m, mul_sub, Finset.sum_sub_distrib]
  have hInt : Integrable (fun ω => (J ω - m) ^ 2) P := by
    have hEq : (fun ω => (J ω - m) ^ 2) =
        (fun ω => (J ω) ^ 2 - 2 * m * J ω + m ^ 2) := by
      funext ω
      ring
    rw [hEq]
    exact (hJ2.sub (hJ.const_mul _)).add (integrable_const _)
  have hRes := avram_a21_raw_second_centered_variance_20261112
    J m v hJ hJ2 hMean hSecond
  simpa only [hZ] using
    (show Integrable (fun ω => (J ω - m) ^ 2) P ∧
      (∫ ω, (J ω - m) ^ 2 ∂P) = v from ⟨hInt, hRes⟩)
