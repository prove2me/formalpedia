-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_countable_mark_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:22:45.294533+00:00
-- url     : https://prove2.me/submissions/4b38f0f1-6b53-4484-85c7-332fd13c4d0d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
/-- Countable disjoint-mark additivity of weighted original jump expectations. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : ι → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (hDisj : Pairwise (Function.onFun Disjoint B))
    (H : Ω → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (⋃ i, B i)) ∂P) =
    ∑' i, (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B i)) ∂P) := by
  have hSet : Ioc s (s + T) ×ˢ (⋃ i, B i) =
      ⋃ i, Ioc s (s + T) ×ˢ B i := by
    ext p
    simp only [Set.mem_prod, Set.mem_iUnion]
    constructor
    · rintro ⟨ht, i, hi⟩; exact ⟨i, ht, hi⟩
    · rintro ⟨i, ht, hi⟩; exact ⟨ht, i, hi⟩
  have hN : ∀ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (⋃ i, B i)) =
      ∑' i, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B i)) := by
    intro ω
    rw [hSet]
    exact MeasureTheory.measure_iUnion
      (fun i j hij => Set.Disjoint.set_prod_right (hDisj hij)
        (Ioc s (s + T)) (Ioc s (s + T)))
      (fun i => measurableSet_Ioc.prod (hB i))
  calc
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (⋃ i, B i)) ∂P) =
      ∫⁻ ω, ∑' i, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B i)) ∂P := by
        congr 1
        funext ω
        rw [hN ω]
        exact (ENNReal.tsum_mul_left).symm
    _ = ∑' i, (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ (B i)) ∂P) :=
      MeasureTheory.lintegral_tsum
        (fun i => (hH.mul
          (avram_p2_f_weighted_original_intrinsic_rectangle_measurable
            X s T (B i) (hB i))).aemeasurable)
