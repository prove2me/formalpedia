-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_discrete_stopping_region_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T12:00:19.612508+00:00
-- url     : https://prove2.me/submissions/04ac7573-f6dc-4ec7-8b80-8bc05f9ebede

import Mathlib.Probability.Process.Predictable
import Mathlib.Probability.Process.Stopping

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- The left-closed region preceding a discrete stopping time belongs to
the predictable sigma-algebra, with the time endpoint included. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (𝓕 : Filtration ℕ mΩ)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime 𝓕 τ) :
    MeasurableSet[𝓕.predictable]
      {p : ℕ × Ω | (p.1 : WithTop ℕ) ≤ τ p.2} := by
  let S : Set (ℕ × Ω) := {p | (p.1 : WithTop ℕ) ≤ τ p.2}
  have hCompl : Sᶜ =
      ⋃ k : ℕ, Set.Ioi k ×ˢ {ω : Ω | τ ω ≤ k} := by
    ext ⟨n, ω⟩
    simp only [S, Set.mem_compl_iff, Set.mem_setOf_eq,
      Set.mem_iUnion, Set.mem_prod, Set.mem_Ioi]
    constructor
    · intro hn
      have hlt : τ ω < (n : WithTop ℕ) := lt_of_not_ge hn
      cases hval : τ ω with
      | top => simp [hval] at hlt
      | coe k =>
          refine ⟨k, ?_, ?_⟩
          · simpa [hval] using hlt
          · simp [hval]
    · rintro ⟨k, hkn, hτk⟩
      have hklt : (k : WithTop ℕ) < (n : WithTop ℕ) := by
        exact_mod_cast hkn
      exact not_le_of_gt (lt_of_le_of_lt hτk hklt)
  have hUnion : MeasurableSet[𝓕.predictable]
      (⋃ k : ℕ, Set.Ioi k ×ˢ {ω : Ω | τ ω ≤ k}) := by
    exact MeasurableSet.iUnion
      (fun k => measurableSet_predictable_Ioi_prod (hτ k))
  rw [← hCompl] at hUnion
  simpa only [compl_compl] using hUnion.compl
