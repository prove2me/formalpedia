-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f17_uniform_rational_early_mass_to_germ_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T00:47:17.900736+00:00
-- url     : https://prove2.me/submissions/db6dd522-6f71-447b-acfe-e655ac863221

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

/-- Uniform early positive excursion mass persists at arbitrarily small rational times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ q : ℚ≥0, Measurable (B (q : ℝ≥0)))
    (a : ℝ≥0∞) (ha : 0 < a)
    (hUniform : ∀ ε : ℝ≥0, 0 < ε →
      a ≤ P {ω : Ω | ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < B (q : ℝ≥0) ω}) :
    0 < P.real {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < B (q : ℝ≥0) ω} := by
  classical
  let E : ℕ → Set Ω := fun n =>
    {ω | ∃ q : ℚ≥0, (q : ℝ≥0) < 1 / ((n : ℝ≥0) + 1) ∧ 0 < B (q : ℝ≥0) ω}
  have hmeas (n : ℕ) : MeasurableSet (E n) := by
    have hsection (q : ℚ≥0) :
        MeasurableSet {ω : Ω | (q : ℝ≥0) < 1 / ((n : ℝ≥0) + 1) ∧
          0 < B (q : ℝ≥0) ω} := by
      by_cases hq : (q : ℝ≥0) < 1 / ((n : ℝ≥0) + 1)
      · have heq : {ω : Ω | (q : ℝ≥0) < 1 / ((n : ℝ≥0) + 1) ∧
            0 < B (q : ℝ≥0) ω} =
            (B (q : ℝ≥0)) ⁻¹' Ioi (0 : ℝ) := by
          ext ω
          constructor
          · intro hw
            exact hw.2
          · intro hw
            exact ⟨hq, hw⟩
        rw [heq]
        exact measurableSet_Ioi.preimage (hB q)
      · have heq : {ω : Ω | (q : ℝ≥0) < 1 / ((n : ℝ≥0) + 1) ∧
            0 < B (q : ℝ≥0) ω} = ∅ := by
          ext ω
          constructor
          · intro hw
            exact (hq hw.1).elim
          · intro hw
            exact False.elim hw
        rw [heq]
        exact MeasurableSet.empty
    have hunion : MeasurableSet (⋃ q : ℚ≥0,
        {ω : Ω | (q : ℝ≥0) < 1 / ((n : ℝ≥0) + 1) ∧ 0 < B (q : ℝ≥0) ω}) :=
      MeasurableSet.iUnion hsection
    have hEq : E n = ⋃ q : ℚ≥0,
        {ω : Ω | (q : ℝ≥0) < 1 / ((n : ℝ≥0) + 1) ∧ 0 < B (q : ℝ≥0) ω} := by
      ext ω
      simp only [E, Set.mem_iUnion, Set.mem_setOf_eq]
    rw [hEq]
    exact hunion
  have hanti : Antitone E := by
    intro i j hij ω hω
    obtain ⟨q, hq, hpos⟩ := hω
    refine ⟨q, lt_of_lt_of_le hq ?_, hpos⟩
    have hij' : (i : ℝ≥0) + 1 ≤ (j : ℝ≥0) + 1 := by
      exact_mod_cast Nat.add_le_add_right hij 1
    exact one_div_le_one_div_of_le (by positivity) hij'
  have hinter : a ≤ P (⋂ n, E n) := by
    have hfin : P (E 0) ≠ ⊤ := ne_of_lt (measure_lt_top P (E 0))
    rw [hanti.measure_iInter (fun n => (hmeas n).nullMeasurableSet) ⟨0, hfin⟩]
    refine le_iInf fun n => ?_
    exact hUniform (1 / ((n : ℝ≥0) + 1)) (by positivity)
  have hsubset : (⋂ n, E n) ⊆
      {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
        ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < B (q : ℝ≥0) ω} := by
    intro ω hω ε hε
    have hεr : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hεr
    have hnNN : (1 : ℝ≥0) / ((n : ℝ≥0) + 1) < ε := by
      exact_mod_cast hn
    obtain ⟨q, hq, hpos⟩ := Set.mem_iInter.mp hω n
    exact ⟨q, lt_trans hq hnNN, hpos⟩
  have hmass : 0 < P {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < B (q : ℝ≥0) ω} :=
    lt_of_lt_of_le ha (le_trans hinter (measure_mono hsubset))
  change 0 < (P {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < B (q : ℝ≥0) ω}).toReal
  exact ENNReal.toReal_pos (ne_of_gt hmass) (ne_of_lt (measure_lt_top P _))
