-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_three_disjoint_mark_void_events_factor_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:21:30.051105+00:00
-- url     : https://prove2.me/submissions/30dfccf0-8495-453a-9bbb-3fa87a3588b8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_disjoint_negative_mark_void_events_independent_20261117
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Three disjoint original negative mark void events have a factored joint probability. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B C D : Set ℝ)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hD : MeasurableSet D)
    (hNegB : B ⊆ Iio (0 : ℝ))
    (hNegC : C ⊆ Iio (0 : ℝ))
    (hNegD : D ⊆ Iio (0 : ℝ))
    (hBC : Disjoint B C) (hBD : Disjoint B D)
    (hCD : Disjoint C D) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (P {ω | NX ω (Ioc 0 T ×ˢ B) = 0 ∧
      NX ω (Ioc 0 T ×ˢ C) = 0 ∧
      NX ω (Ioc 0 T ×ˢ D) = 0}).toReal =
      ((P {ω | NX ω (Ioc 0 T ×ˢ B) = 0}).toReal *
       (P {ω | NX ω (Ioc 0 T ×ˢ C) = 0}).toReal) *
       (P {ω | NX ω (Ioc 0 T ×ˢ D) = 0}).toReal := by
  classical
  dsimp
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let A : Set ℝ≥0 := Ioc 0 T
  have hA : MeasurableSet A := measurableSet_Ioc
  have hBCMeas := hB.union hC
  have hBCNeg : B ∪ C ⊆ Iio (0 : ℝ) := Set.union_subset hNegB hNegC
  have hBCD : Disjoint (B ∪ C) D := by
    apply Set.disjoint_left.mpr
    intro x hx hdx
    rcases hx with hbx | hcx
    · exact (Set.disjoint_left.mp hBD) hbx hdx
    · exact (Set.disjoint_left.mp hCD) hcx hdx
  have hRect : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
    ext p
    simp
  have hDisjRect : Disjoint (A ×ˢ B) (A ×ˢ C) := by
    apply Set.disjoint_left.mpr
    intro p hpB hpC
    exact (Set.disjoint_left.mp hBC) hpB.2 hpC.2
  have hAdd (ω : Ω) :
      NX ω (A ×ˢ (B ∪ C)) = NX ω (A ×ˢ B) + NX ω (A ×ˢ C) := by
    rw [hRect, measure_union hDisjRect (hA.prod hC)]
  have hE :
      {ω | NX ω (A ×ˢ (B ∪ C)) = 0 ∧ NX ω (A ×ˢ D) = 0} =
      {ω | NX ω (A ×ˢ B) = 0 ∧ NX ω (A ×ˢ C) = 0 ∧
        NX ω (A ×ˢ D) = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, hAdd, add_eq_zero, and_assoc]
  have hPair := avram_a27_original_disjoint_negative_mark_void_events_independent_20261117
    X hFinite T B C hB hC hNegB hNegC hBC
  have hUnion := avram_a27_original_disjoint_negative_mark_void_events_independent_20261117
    X hFinite T (B ∪ C) D hBCMeas hD hBCNeg hNegD hBCD
  change
    (P {ω | NX ω (A ×ˢ B) = 0 ∧ NX ω (A ×ˢ C) = 0 ∧
      NX ω (A ×ˢ D) = 0}).toReal = _
  calc
    _ = (P {ω | NX ω (A ×ˢ (B ∪ C)) = 0 ∧
        NX ω (A ×ˢ D) = 0}).toReal := by rw [hE]
    _ = (P {ω | NX ω (A ×ˢ (B ∪ C)) = 0}).toReal *
        (P {ω | NX ω (A ×ˢ D) = 0}).toReal := by
          simpa [NX, A] using hUnion
    _ = ((P {ω | NX ω (A ×ˢ B) = 0}).toReal *
         (P {ω | NX ω (A ×ˢ C) = 0}).toReal) *
         (P {ω | NX ω (A ×ˢ D) = 0}).toReal := by
          simpa [NX, A] using congrArg (fun z : ℝ =>
            z * (P {ω | NX ω (A ×ˢ D) = 0}).toReal) hPair
