-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_finite_disjoint_negative_Borel_mark_void_product_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T17:31:44.959804+00:00
-- url     : https://prove2.me/submissions/9743a1d0-3006-4696-a56d-63435bd7308e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_admissible_disjoint_union_functional_finite_product_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_disjoint_negative_mark_void_events_independent_20261117
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
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let A : Set ℝ≥0 := Ioc 0 T
  let Good : Set ℝ → Prop := fun U =>
    MeasurableSet U ∧ U ⊆ Iio (0 : ℝ)
  let Q : Set ℝ → ℝ := fun U => (P {ω | NX ω (A ×ˢ U) = 0}).toReal
  have hGS : ∀ i ∈ S, Good (B i) := by
    intro i hi
    exact ⟨hMeas i hi, hNeg i hi⟩
  have hGU : ∀ R : Finset ι,
      (∀ i ∈ R, Good (B i)) →
      Good (⋃ i ∈ R, B i) := by
    intro R hR
    constructor
    · exact Finset.measurableSet_biUnion R (fun i hi => (hR i hi).1)
    · intro y hy
      rcases Set.mem_iUnion.mp hy with ⟨i, hi⟩
      rcases Set.mem_iUnion.mp hi with ⟨hiR, hBi⟩
      exact (hR i hiR).2 hBi
  have h0 : Q ∅ = 1 := by
    simp [Q, measureReal_def]
  have hMul : ∀ U V : Set ℝ,
      Good U → Good V → Disjoint U V →
        Q (U ∪ V) = Q U * Q V := by
    intro U V hU hV hDisj
    have hRect : A ×ˢ (U ∪ V) =
        (A ×ˢ U) ∪ (A ×ˢ V) := by
      ext p
      simp [and_or_left]
    have hEv :
        {ω | NX ω (A ×ˢ (U ∪ V)) = 0} =
        {ω | NX ω (A ×ˢ U) = 0 ∧ NX ω (A ×ˢ V) = 0} := by
      ext ω
      simp only [Set.mem_setOf_eq, hRect, measure_union_null_iff]
    have hTwo :=
      avram_a27_original_disjoint_negative_mark_void_events_independent_20261117
        X hFinite T U V hU.1 hV.1 hU.2 hV.2 hDisj
    change (P {ω | NX ω (A ×ˢ (U ∪ V)) = 0}).toReal =
      (P {ω | NX ω (A ×ˢ U) = 0}).toReal *
      (P {ω | NX ω (A ×ˢ V) = 0}).toReal
    rw [hEv]
    simpa [NX, A] using hTwo
  change Q (⋃ i ∈ S, B i) = ∏ i ∈ S, Q (B i)
  exact avram_a27_admissible_disjoint_union_functional_finite_product_20261117
    Good B Q h0 hGU hMul S hGS hPair
