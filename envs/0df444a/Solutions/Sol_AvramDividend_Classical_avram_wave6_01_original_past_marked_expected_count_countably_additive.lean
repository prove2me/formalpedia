-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_01_original_past_marked_expected_count_countably_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T21:58:20.720783+00:00
-- url     : https://prove2.me/submissions/9b033857-62b9-416c-9250-a68ee297fe03

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
    (B : ℕ → Set ℝ) (hB : ∀ n, MeasurableSet (B n))
    (hDisj : Pairwise (fun i j => Disjoint (B i) (B j))) :
    (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ (⋃ n, B n)) ∂P) =
    ∑' n, (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B n) ∂P) := by
  classical
  let N : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  obtain ⟨κ, hκFinite, hκ⟩ :=
    avram_wave5_02a_actual_source_intrinsic_sfinite_kernel X
  have hSetB (n : ℕ) : MeasurableSet (Ioc s t ×ˢ B n) :=
    measurableSet_Ioc.prod (hB n)
  have hMeas (n : ℕ) :
      Measurable (fun ω => N ω (Ioc s t ×ˢ B n)) := by
    have hk := ProbabilityTheory.Kernel.measurable_coe κ (hSetB n)
    convert hk using 1
    funext ω
    exact congrArg
      (fun μ : Measure (ℝ≥0 × ℝ) => μ (Ioc s t ×ˢ B n)) (hκ ω).symm
  have hUnion : Ioc s t ×ˢ (⋃ n, B n) =
      ⋃ n, (Ioc s t ×ˢ B n) := by
    ext p
    simp only [mem_prod, mem_iUnion]
    constructor
    · rintro ⟨hp, i, hi⟩
      exact ⟨i, hp, hi⟩
    · rintro ⟨i, hp, hi⟩
      exact ⟨hp, i, hi⟩
  have hProdDisj : Pairwise
      (fun i j => Disjoint (Ioc s t ×ˢ B i) (Ioc s t ×ˢ B j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    rintro ⟨u, y⟩ ⟨hu, hyI⟩ ⟨_, hyJ⟩
    exact Set.disjoint_left.mp (hDisj hij) hyI hyJ
  have hPoint (ω : Ω) :
      N ω (Ioc s t ×ˢ (⋃ n, B n)) =
        ∑' n, N ω (Ioc s t ×ˢ B n) := by
    rw [hUnion]
    exact measure_iUnion hProdDisj hSetB
  change (∫⁻ ω in A, N ω (Ioc s t ×ˢ (⋃ n, B n)) ∂P) =
    ∑' n, (∫⁻ ω in A, N ω (Ioc s t ×ˢ B n) ∂P)
  calc
    (∫⁻ ω in A, N ω (Ioc s t ×ˢ (⋃ n, B n)) ∂P) =
        ∫⁻ ω in A, (∑' n, N ω (Ioc s t ×ˢ B n)) ∂P := by
      apply lintegral_congr
      intro ω
      exact hPoint ω
    _ = _ := by
      rw [lintegral_tsum (fun n => (hMeas n).aemeasurable)]
