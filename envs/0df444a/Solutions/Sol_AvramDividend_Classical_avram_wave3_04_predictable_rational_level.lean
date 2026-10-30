-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_predictable_rational_level
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:31:24.79448+00:00
-- url     : https://prove2.me/submissions/a3a08ad5-af7a-4b74-90f9-1e9320b0c2fd

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- A monotone adapted process with zero initial value and countable
strict-left approximation has measurable predictable evaluation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℝ≥0 mΩ)
    (D : ℝ≥0 → Ω → ℝ)
    (hzero : ∀ ω, D 0 ω = 0)
    (hadapt : Adapted 𝓕 D)
    (hmono : ∀ ω, Monotone (fun t => D t ω))
    (hdense : ∀ ω t (a : ℝ), t ≠ 0 → a < D t ω →
      ∃ r : ℚ≥0, (r : ℝ≥0) < t ∧ a < D (r : ℝ≥0) ω) :
    @Measurable (ℝ≥0 × Ω) ℝ 𝓕.predictable inferInstance
      (fun p => D p.1 p.2) := by
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.predictable
  apply measurable_of_Ioi
  intro a
  by_cases ha : a < 0
  · have hfull : (fun p : ℝ≥0 × Ω => D p.1 p.2) ⁻¹' Set.Ioi a =
        Set.univ := by
      ext p
      have hpnonneg : 0 ≤ D p.1 p.2 := by
        have h := hmono p.2 (bot_le : (0 : ℝ≥0) ≤ p.1)
        simpa [hzero p.2] using h
      simp [Set.mem_preimage, Set.mem_Ioi, lt_of_lt_of_le ha hpnonneg]
    rw [hfull]
    exact MeasurableSet.univ
  · have ha0 : 0 ≤ a := le_of_not_gt ha
    have hparts : ∀ r : ℚ≥0,
        MeasurableSet (Set.Ioi (r : ℝ≥0) ×ˢ
          {ω : Ω | a < D (r : ℝ≥0) ω}) := by
      intro r
      have hm : @Measurable Ω ℝ (𝓕 (r : ℝ≥0)) inferInstance
          (D (r : ℝ≥0)) := hadapt _
      exact measurableSet_predictable_Ioi_prod (hm isOpen_Ioi.measurableSet)
    have heq : (fun p : ℝ≥0 × Ω => D p.1 p.2) ⁻¹' Set.Ioi a =
        ⋃ r : ℚ≥0, Set.Ioi (r : ℝ≥0) ×ˢ
          {ω : Ω | a < D (r : ℝ≥0) ω} := by
      ext p
      constructor
      · intro hp
        have hpval : a < D p.1 p.2 := hp
        have ht : p.1 ≠ 0 := by
          intro he
          have hbad : a < 0 := by simpa [he, hzero p.2] using hpval
          exact (not_lt_of_ge ha0) hbad
        obtain ⟨r, hrlt, hrval⟩ := hdense p.2 p.1 a ht hpval
        exact Set.mem_iUnion.mpr ⟨r, ⟨hrlt, hrval⟩⟩
      · intro hp
        rcases Set.mem_iUnion.mp hp with ⟨r, hrlt, hrval⟩
        exact lt_of_lt_of_le hrval (hmono p.2 (le_of_lt hrlt))
    rw [heq]
    exact MeasurableSet.iUnion hparts
