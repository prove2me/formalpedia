-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_stopped_marked_predictable_kernel_closure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T19:23:22.055155+00:00
-- url     : https://prove2.me/submissions/b825fd40-adea-4729-9a9b-0a2ab5c406e2

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_countable_time_stopping_inclusive_predictable_mask

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical

/-- A genuinely predictable marked kernel stays predictable when multiplied
by the inclusive survival indicator of a genuine stopping time, on the same
sample space and original filtration. The marked product sigma algebra and
stopping-time past events are explicit; no compensation identity is assumed. -/
theorem solution
    {Ω ι E : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [mE : MeasurableSpace E]
    (𝓕 : Filtration ι mΩ)
    (D : Set ι) (hD : D.Countable)
    (hSep : ∀ a b : ι, a < b →
      ∃ s : ι, s ∈ D ∧ a ≤ s ∧ s < b)
    (τ : Ω → ι)
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ι)))
    (F : ((ι × Ω) × E) → ℝ)
    (hF : Measurable[(𝓕.predictable).prod mE] F) :
    Measurable[(𝓕.predictable).prod mE]
      (fun p => if p.1.1 ≤ τ p.1.2 then F p else 0) := by
  classical
  have hTime : MeasurableSet[𝓕.predictable]
      {q : ι × Ω | q.1 ≤ τ q.2} :=
    avram_wave4_p1_countable_time_stopping_inclusive_predictable_mask
      𝓕 D hD hSep τ hτ
  have hMarked : MeasurableSet[(𝓕.predictable).prod mE]
      ({q : ι × Ω | q.1 ≤ τ q.2} ×ˢ (Set.univ : Set E)) :=
    hTime.prod MeasurableSet.univ
  have heq :
      ({q : ι × Ω | q.1 ≤ τ q.2} ×ˢ (Set.univ : Set E)) =
      {p : (ι × Ω) × E | p.1.1 ≤ τ p.1.2} := by
    ext p
    simp only [Set.mem_prod, Set.mem_setOf_eq, Set.mem_univ, and_true]
  rw [heq] at hMarked
  exact Measurable.ite hMarked hF measurable_const