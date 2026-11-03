-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_disjoint_borel_mark_intrinsic_count_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T16:15:55.702767+00:00
-- url     : https://prove2.me/submissions/4f24fdc0-5a28-4789-8356-bfef9ac90595

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Disjoint Borel mark cells split the true intrinsic original Lévy jump count. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0)
    (B C : Set ℝ) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hDisj : Disjoint B C) :
    (let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
     NX (Ioc s t ×ˢ (B ∪ C)) =
       NX (Ioc s t ×ˢ B) + NX (Ioc s t ×ˢ C)) := by
  classical
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
  change NX (Ioc s t ×ˢ (B ∪ C)) =
    NX (Ioc s t ×ˢ B) + NX (Ioc s t ×ˢ C)
  have hUnion : Ioc s t ×ˢ (B ∪ C) =
      (Ioc s t ×ˢ B) ∪ (Ioc s t ×ˢ C) := by
    ext p
    rcases p with ⟨v, z⟩
    simp only [mem_prod, mem_union]
    tauto
  have hDisjProd : Disjoint (Ioc s t ×ˢ B) (Ioc s t ×ˢ C) := by
    apply Set.disjoint_left.mpr
    rintro p hpB hpC
    exact (Set.disjoint_left.mp hDisj) hpB.2 hpC.2
  have hMeas : MeasurableSet (Ioc s t ×ˢ C) :=
    measurableSet_Ioc.prod hC
  rw [hUnion]
  exact measure_union hDisjProd hMeas
