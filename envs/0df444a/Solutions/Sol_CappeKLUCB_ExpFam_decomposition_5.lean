-- Prove2me | solution 1 for CappeKLUCB.ExpFam.decomposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T23:22:35.311453+00:00
-- url     : https://prove2.me/submissions/24ad71bd-585f-4a8b-b743-4b4cadfc01d7

import Mathlib
import Definitions.Def_CappeKLUCB_ExpFam_Setting

set_option autoImplicit false

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic OptimalBAI.OptProportions CappeKLUCB.ExpFam in
theorem solution {K : ℕ} (F : ExpFamily) {Ω : Type*}
    (X : Fin K → ℕ → Ω → ℝ) (I : ℕ → Ω → Fin K) (hrun : IsKLUCBRun F f₁ X I)
    (a astar : Fin K) (μdag : ℝ) (t : ℕ) (ht : K ≤ t) (ω : Ω) (hplay : I (t + 1) ω = a) :
    (klucbIndex F f₁ X I astar t ω ≤ μdag ∨
        (μdag < klucbIndex F f₁ X I astar t ω ∧ I (t + 1) ω = a)) ∧
      (klucbIndex F f₁ X I astar t ω ≤ μdag ∨
        (μdag < klucbIndex F f₁ X I a t ω ∧ I (t + 1) ω = a)) := by
  have hmax : klucbIndex F f₁ X I astar t ω ≤ klucbIndex F f₁ X I a t ω := by
    have h := (hrun ω t).2 ht astar
    rw [hplay] at h
    exact h
  rcases le_or_gt (klucbIndex F f₁ X I astar t ω) μdag with h | h
  · exact ⟨Or.inl h, Or.inl h⟩
  · exact ⟨Or.inr ⟨h, hplay⟩, Or.inr ⟨lt_of_lt_of_le h hmax, hplay⟩⟩
