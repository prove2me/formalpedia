-- Prove2me | solution 2 for AvramDividend.Classical.avram_a27_original_finite_disjoint_negative_Borel_mark_void_product_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:31:58.517208+00:00
-- url     : https://prove2.me/submissions/3d7576ca-c6a8-45ce-b49d-12d57e29c4a6

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_disjoint_negative_mark_void_events_independent_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_finite_void_union_iff_all_mark_cells_void_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Actual original physical negative-jump void probabilities factor over every disjoint finite mark family. -/

theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B : ι → Set ℝ) (S : Finset ι)
    (hMeas : ∀ i ∈ S, MeasurableSet (B i))
    (hNeg : ∀ i ∈ S, B i ⊆ Iio (0 : ℝ))
    (hPair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (P {ω | NX ω (Ioc 0 T ×ˢ (⋃ i ∈ S, B i)) = 0}).toReal =
      ∏ i ∈ S, (P {ω | NX ω (Ioc 0 T ×ˢ B i) = 0}).toReal := by
  classical
  letI : IsProbabilityMeasure P := X.isProbability
  intro NX
  revert hMeas hNeg hPair
  induction S using Finset.induction_on with
  | empty =>
      intro hMeas hNeg hPair
      simp only [Finset.prod_empty, Set.biUnion_empty, Set.prod_empty,
        measure_empty]
      simp
  | @insert a S ha ih =>
      intro hMeas hNeg hPair
      have hmA : MeasurableSet (B a) := hMeas a (Finset.mem_insert_self a S)
      have hnA : B a ⊆ Iio (0 : ℝ) := hNeg a (Finset.mem_insert_self a S)
      have hmS : ∀ i ∈ S, MeasurableSet (B i) := by
        intro i hi
        exact hMeas i (Finset.mem_insert_of_mem hi)
      have hnS : ∀ i ∈ S, B i ⊆ Iio (0 : ℝ) := by
        intro i hi
        exact hNeg i (Finset.mem_insert_of_mem hi)
      have hpS : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → Disjoint (B i) (B j) := by
        intro i hi j hj hij
        exact hPair i (Finset.mem_insert_of_mem hi) j
          (Finset.mem_insert_of_mem hj) hij
      have hMS : MeasurableSet (⋃ i ∈ S, B i) :=
        Finset.measurableSet_biUnion S hmS
      have hNS : (⋃ i ∈ S, B i) ⊆ Iio (0 : ℝ) := by
        intro z hz
        rcases Set.mem_iUnion.mp hz with ⟨i, hi⟩
        rcases Set.mem_iUnion.mp hi with ⟨hSi, hZi⟩
        exact hnS i hSi hZi
      have hDS : Disjoint (B a) (⋃ i ∈ S, B i) := by
        simp only [Set.disjoint_iUnion_right]
        intro i hi
        exact hPair a (Finset.mem_insert_self a S) i
          (Finset.mem_insert_of_mem hi) (by
            intro hai
            exact ha (hai ▸ hi))
      have hFactor :=
        avram_a27_original_disjoint_negative_mark_void_events_independent_20261117
          X hFinite T (B a) (⋃ i ∈ S, B i) hmA hMS hnA hNS hDS
      have hUnion : (⋃ i ∈ insert a S, B i) =
          B a ∪ (⋃ i ∈ S, B i) := by
        ext z
        simp only [Set.mem_iUnion, Finset.mem_insert, Set.mem_union]
        aesop
      have hSplit :
          {ω | NX ω (Ioc 0 T ×ˢ (⋃ i ∈ insert a S, B i)) = 0} =
          {ω | NX ω (Ioc 0 T ×ˢ B a) = 0 ∧
            NX ω (Ioc 0 T ×ˢ (⋃ i ∈ S, B i)) = 0} := by
        ext ω
        simp only [hUnion, Set.prod_union, measure_union_null_iff, Set.mem_setOf_eq]
      rw [hSplit, Finset.prod_insert ha]
      calc
        (P {ω | NX ω (Ioc 0 T ×ˢ B a) = 0 ∧
          NX ω (Ioc 0 T ×ˢ (⋃ i ∈ S, B i)) = 0}).toReal =
            (P {ω | NX ω (Ioc 0 T ×ˢ B a) = 0}).toReal *
              (P {ω | NX ω (Ioc 0 T ×ˢ (⋃ i ∈ S, B i)) = 0}).toReal := by
                  simpa only [NX] using hFactor
        _ = _ := by rw [ih hmS hnS hpS]
