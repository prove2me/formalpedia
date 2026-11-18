-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_disjoint_negative_mark_void_events_independent_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:13:34.007999+00:00
-- url     : https://prove2.me/submissions/b53d1a94-baf4-4cb0-bd6e-92683c36cb85

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_shifted_negative_Borel_physical_void_exact_20261115
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Disjoint negative mark sets have independent original physical void events at a fixed horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (B C : Set ℝ)
    (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hNegB : B ⊆ Iio (0 : ℝ)) (hNegC : C ⊆ Iio (0 : ℝ))
    (hDisj : Disjoint B C) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (P {ω | NX ω (Ioc 0 T ×ˢ B) = 0 ∧
      NX ω (Ioc 0 T ×ˢ C) = 0}).toReal =
      (P {ω | NX ω (Ioc 0 T ×ˢ B) = 0}).toReal *
      (P {ω | NX ω (Ioc 0 T ×ˢ C) = 0}).toReal := by
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
  have hBC : MeasurableSet (B ∪ C) := hB.union hC
  have hNegBC : B ∪ C ⊆ Iio (0 : ℝ) := Set.union_subset hNegB hNegC
  have hRect : A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
    ext p
    simp
  have hDisjRect : Disjoint (A ×ˢ B) (A ×ˢ C) := by
    apply Set.disjoint_left.mpr
    intro p hpB hpC
    exact (Set.disjoint_left.mp hDisj) hpB.2 hpC.2
  have hAdd (ω : Ω) :
      NX ω (A ×ˢ (B ∪ C)) = NX ω (A ×ˢ B) + NX ω (A ×ˢ C) := by
    rw [hRect, measure_union hDisjRect (hA.prod hC)]
  have hEvent :
      {ω | NX ω (A ×ˢ (B ∪ C)) = 0} =
      {ω | NX ω (A ×ˢ B) = 0 ∧ NX ω (A ×ˢ C) = 0} := by
    ext ω
    simp only [Set.mem_setOf_eq, hAdd]
    exact add_eq_zero
  have hBFin : X.ν B ≠ ⊤ :=
    ne_top_of_le_ne_top hFinite (measure_mono hNegB)
  have hCFin : X.ν C ≠ ⊤ :=
    ne_top_of_le_ne_top hFinite (measure_mono hNegC)
  have hReal :
      (X.ν (B ∪ C)).toReal = (X.ν B).toReal + (X.ν C).toReal := by
    rw [measure_union hDisj hC, ENNReal.toReal_add hBFin hCFin]
  have hvB := avram_a25_original_shifted_negative_Borel_physical_void_exact_20261115
    X hFinite 0 T B hB hNegB
  have hvC := avram_a25_original_shifted_negative_Borel_physical_void_exact_20261115
    X hFinite 0 T C hC hNegC
  have hvBC := avram_a25_original_shifted_negative_Borel_physical_void_exact_20261115
    X hFinite 0 T (B ∪ C) hBC hNegBC
  change
    (P {ω | NX ω (A ×ˢ B) = 0 ∧ NX ω (A ×ˢ C) = 0}).toReal =
      (P {ω | NX ω (A ×ˢ B) = 0}).toReal *
      (P {ω | NX ω (A ×ˢ C) = 0}).toReal
  calc
    _ = (P {ω | NX ω (A ×ˢ (B ∪ C)) = 0}).toReal := by
      rw [hEvent]
    _ = Real.exp (-((T : ℝ) * (X.ν (B ∪ C)).toReal)) := by
      simpa [NX, A] using hvBC
    _ = Real.exp (-((T : ℝ) * (X.ν B).toReal)) *
        Real.exp (-((T : ℝ) * (X.ν C).toReal)) := by
      rw [hReal, ← Real.exp_add]
      congr 1
      ring
    _ = _ := by
      simpa [NX, A] using congrArg₂ (· * ·) hvB.symm hvC.symm
