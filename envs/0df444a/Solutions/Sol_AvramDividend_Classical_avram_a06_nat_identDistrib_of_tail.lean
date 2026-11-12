-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_nat_identDistrib_of_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T09:50:44.034103+00:00
-- url     : https://prove2.me/submissions/c46938b2-5cf2-4eca-a995-d82e35e23c45

import Mathlib.Probability.IdentDistrib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
noncomputable section

/-- Strict natural-number tails determine the distribution of a measurable count. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℕ) (hX : Measurable X) (hY : Measurable Y)
    (hTail : ∀ k : ℕ, P {ω | k < X ω} = P {ω | k < Y ω}) :
    IdentDistrib X Y P P := by
  let μ : Measure ℕ := P.map X
  let ν : Measure ℕ := P.map Y
  have hμTotal : μ univ = P univ := by
    change (P.map X) univ = P univ
    rw [Measure.map_apply hX MeasurableSet.univ]
    simp
  have hνTotal : ν univ = P univ := by
    change (P.map Y) univ = P univ
    rw [Measure.map_apply hY MeasurableSet.univ]
    simp
  haveI : IsFiniteMeasure μ := ⟨by rw [hμTotal]; exact measure_lt_top P univ⟩
  haveI : IsFiniteMeasure ν := ⟨by rw [hνTotal]; exact measure_lt_top P univ⟩
  have hMass : μ univ = ν univ := hμTotal.trans hνTotal.symm
  have hμTail (k : ℕ) : μ (Ioi k) = P {ω | k < X ω} := by
    change (P.map X) (Ioi k) = _
    rw [Measure.map_apply hX measurableSet_Ioi]
    rfl
  have hνTail (k : ℕ) : ν (Ioi k) = P {ω | k < Y ω} := by
    change (P.map Y) (Ioi k) = _
    rw [Measure.map_apply hY measurableSet_Ioi]
    rfl
  have hTailMap (k : ℕ) : μ (Ioi k) = ν (Ioi k) := by
    calc
      μ (Ioi k) = P {ω | k < X ω} := hμTail k
      _ = P {ω | k < Y ω} := hTail k
      _ = ν (Ioi k) := (hνTail k).symm
  have hEqual : μ = ν := by
    apply Measure.ext_of_Iic μ ν
    intro k
    calc
      μ (Iic k) = μ univ - μ (Ioi k) := by
        simpa only [Set.compl_Ioi] using
          (measure_compl measurableSet_Ioi (measure_ne_top μ (Ioi k)))
      _ = ν univ - ν (Ioi k) := by rw [hMass, hTailMap]
      _ = ν (Iic k) := by
        simpa only [Set.compl_Ioi] using
          (measure_compl measurableSet_Ioi (measure_ne_top ν (Ioi k))).symm
  exact ⟨hX.aemeasurable, hY.aemeasurable, hEqual⟩
