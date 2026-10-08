-- Prove2me | solution 1 for CappeKLUCB.Empirical.decomposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:43:18.784198+00:00
-- url     : https://prove2.me/submissions/d80e58fe-2d6a-45f3-96ec-c4f13c2b7d1f

import Mathlib
import Definitions.Def_CappeKLUCB_Empirical_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic CappeKLUCB.Empirical in
theorem solution {K : ℕ} {Ω : Type*} (X : Fin K → ℕ → Ω → ℝ) (I : ℕ → Ω → Fin K)
    (f : ℕ → ℝ) (hrun : IsEmpKLUCBRun f X I) (a astar : Fin K) (μdag : ℝ) (ω : Ω) (t : ℕ)
    (ht : K ≤ t) (hplay : I (t + 1) ω = a) :
    (μdag ≥ index f X I astar t ω ∨ (μdag < index f X I astar t ω ∧ I (t + 1) ω = a)) ∧
    (μdag ≥ index f X I astar t ω ∨ (μdag < index f X I a t ω ∧ I (t + 1) ω = a)) := by
  have hmax : index f X I astar t ω ≤ index f X I a t ω := by
    have h := (hrun ω t).2 ht astar
    rw [hplay] at h
    exact h
  rcases le_or_gt (index f X I astar t ω) μdag with h | h
  · exact ⟨Or.inl h, Or.inl h⟩
  · exact ⟨Or.inr ⟨h, hplay⟩, Or.inr ⟨lt_of_lt_of_le h hmax, hplay⟩⟩
