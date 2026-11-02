-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_past_marked_expected_count_finite_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:09:17.57909+00:00
-- url     : https://prove2.me/submissions/5c7e071e-ab71-4a14-82b0-69b9e7e45a34

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hBC : Disjoint B C) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∪ C)) ∂P) =
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) +
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ C) ∂P) := by
  classical
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  obtain ⟨κ, hκFinite, hκ⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  have hSetB : MeasurableSet (Ioc s t ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hMeasB : Measurable (fun ω => N ω (Ioc s t ×ˢ B)) := by
    have hk := ProbabilityTheory.Kernel.measurable_coe κ hSetB
    convert hk using 1
    funext ω
    exact congrArg (fun μ : Measure (ℝ≥0 × ℝ) => μ (Ioc s t ×ˢ B)) (hκ ω).symm
  have hUnion : Ioc s t ×ˢ (B ∪ C) =
      (Ioc s t ×ˢ B) ∪ (Ioc s t ×ˢ C) := by
    ext p
    simp only [mem_prod, mem_union, and_or_left]
  have hDisj : Disjoint (Ioc s t ×ˢ B) (Ioc s t ×ˢ C) := by
    apply Set.disjoint_left.mpr
    rintro ⟨u, y⟩ ⟨hu, hyB⟩ ⟨_, hyC⟩
    exact Set.disjoint_left.mp hBC hyB hyC
  have hPoint (ω : Ω) :
      N ω (Ioc s t ×ˢ (B ∪ C)) =
        N ω (Ioc s t ×ˢ B) + N ω (Ioc s t ×ˢ C) := by
    rw [hUnion]
    exact measure_union hDisj (measurableSet_Ioc.prod hC)
  change (∫⁻ ω in A, N ω (Ioc s t ×ˢ (B ∪ C)) ∂P) =
    (∫⁻ ω in A, N ω (Ioc s t ×ˢ B) ∂P) +
    (∫⁻ ω in A, N ω (Ioc s t ×ˢ C) ∂P)
  calc
    (∫⁻ ω in A, N ω (Ioc s t ×ˢ (B ∪ C)) ∂P) =
        ∫⁻ ω in A, (N ω (Ioc s t ×ˢ B) +
          N ω (Ioc s t ×ˢ C)) ∂P := by
        apply lintegral_congr
        intro ω
        exact hPoint ω
    _ = _ := lintegral_add_left hMeasB _
