-- Prove2me | solution 1 for AvramDividend.Classical.avram_0b18_global_excess_gives_full_event_zero_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T12:15:34.220198+00:00
-- url     : https://prove2.me/submissions/c4b5d81f-7dd4-4ca6-8777-d63a6326e011

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
noncomputable section

/-- Global positive-error decay admits full-event localisation with zero off-event envelope. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E R : ℕ → Ω → ℝ)
    (hGlobal : Tendsto
      (fun n => ∫ ω, max (E n ω) 0 ∂P)
      atTop (nhds (0 : ℝ))) :
    ∃ s : ℕ → Set Ω, ∃ K : ℝ,
      0 ≤ K ∧
      (∀ n, MeasurableSet (s n)) ∧
      (∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n) ∧
      Tendsto
        (fun n => ∫ ω, max (if ω ∈ s n then E n ω else 0) 0 ∂P)
        atTop (nhds (0 : ℝ)) ∧
      (∀ n, ∀ᵐ ω ∂P,
        max (if ω ∉ s n then E n ω else 0) 0 ≤
          (if ω ∈ s n then 0 else K * R n ω)) := by
  refine ⟨fun _ => Set.univ, 0, le_rfl, ?_, ?_, ?_, ?_⟩
  · intro n
    exact MeasurableSet.univ
  · exact Filter.Eventually.of_forall (fun ω =>
      Filter.Eventually.of_forall (fun n => Set.mem_univ ω))
  · simpa only [Set.mem_univ, ite_true] using hGlobal
  · intro n
    exact Filter.Eventually.of_forall (fun ω => by simp)
